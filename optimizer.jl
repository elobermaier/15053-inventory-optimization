using CSV, JuMP, Cbc

avg_demand = CSV.read("AverageDemandForecast.csv")

lb_demand = CSV.read("LowerBoundDemandForecast.csv")

ub_demand = CSV.read("UpperBoundDemandForecast.csv")

old_max_prod = CSV.read("MaxProductionCapacity.csv")
max_prod = old_max_prod[1:34,:] #clip useless last row

weeks = names(avg_demand)[2:length(names(avg_demand))] #keys are Symbols not int so be careful!

"""
prod_dict maps product name (str from csv) to a dict w/keys:
"biweekly_replenishment" (in pallets)
"prod_capac" (pallets)
"units_per_pallet" (pallets)
"avg_dem_week_x" average demand on week x for x in weeks array (skips so be careful!)
"lb_dem_week_x" lower bound demand forecast on week x for x in weeks array
"ub_dem_week_x" upper bound demand forecast on week x for x in weeks array
"type" string, what category of product
"late_cost", late cost per unit of a certain product (dependent on its category)

NOTE1:
Get lower bound demand forecast for "Pampers Diapers" on week 51:
>> prod_dict["Pampers Diapers"][string("lb_dem_week_51")]

Get lower bound demand forecast for "Pampers Diapers" on week x:
>> prod_dict["Pampers Diapers"][string("lb_dem_week_", x)]
"""
# late order cost per unit for diff product types = 2x retail val
late_cost = Dict("baby" => 100, "fabric" => 40, "family"=> 20, "fem" => 15, "grooming" => 40, "hair" => 16, "home" => 30, "oral" => 90, "PHC" => 20, "skin/personal" => 80)

prod_dict = Dict(max_prod[k,1] => Dict("biweekly_replenishment" => max_prod[k,2], "prod_capac" => max_prod[k,3], "units_per_pallet" => max_prod[k, 4], "type" => "") for k in 1:length(max_prod[:,1]))

for i in 1:length(max_prod[:,1])
    prodname = max_prod[i,1]
    for j in weeks
        prod_dict[prodname][string("avg_dem_week_", j)] = avg_demand[i,j]
        prod_dict[prodname][string("lb_dem_week_", j)] = lb_demand[i,j]
        prod_dict[prodname][string("ub_dem_week_", j)] = ub_demand[i,j]
        if i in 1:2
            prod_dict[prodname]["type"] = "baby"
        elseif i in 3:6
            prod_dict[prodname]["type"] = "fabric"
        elseif i in 7:9
            prod_dict[prodname]["type"] = "family"
        elseif i in 10:11
            prod_dict[prodname]["type"] = "fem"
        elseif i in 12:15
            prod_dict[prodname]["type"] = "grooming"
        elseif i in 16:19
            prod_dict[prodname]["type"] = "hair"
        elseif i in 20:24
            prod_dict[prodname]["type"] = "home"
        elseif i in 25:28
            prod_dict[prodname]["type"] = "oral"
        elseif i in 29:30
            prod_dict[prodname]["type"] = "PHC"
        elseif i in 31:34
            prod_dict[prodname]["type"] = "skin/personal"
        end
        prod_dict[prodname]["late_cost"] = late_cost[prod_dict[prodname]["type"]]
    end
end

#inventory cost (units per day)
inv_cost = 0.5

#max capacity of distrib center (pallets)
distrib_max = 7200

#production costs to weeks notice
prod_notice = [1, 2, 3, 4, 5]
prod_cost = [25, 7.5, 2.5, 1, 0.5]

infinity = 1000000

m = Model(with_optimizer(Cbc.Optimizer, logLevel = 0))

@variable(m, x[1:34, 1:51, 1:5] >= 0, Int) #x[i, j, k] order of item i during week j with k weeks notice

@expression(m, received[1:34, 1:51], 0) #received[j, k] how many units of product j will we receive on week k

for prod_idx in 1:length(max_prod[:,1])
    prodname = max_prod[prod_idx,1]
    for week in 1:51
        
        #extra orders
        sm = 0
        for week_rush in 1:5
            if week > week_rush
                sm = sm + x[prod_idx, week - week_rush, week_rush]
            end
        end
        
        #biweekly_replenishment
        value = 0
        if week % 2 == 1
            value = prod_dict[prodname]["biweekly_replenishment"]
        end
        JuMP.add_to_expression!(received[prod_idx, week], (sm + value) * prod_dict[prodname]["units_per_pallet"])
    end
end

#cannot order more than production capacity
for prod_idx in 1:length(max_prod[:,1])
    prodname = max_prod[prod_idx,1]
    for week in 1:51
        for week_rush in 1:5
            @constraint(m, x[prod_idx, week, week_rush] <= prod_dict[prodname]["prod_capac"])
        end
    end
end

@variable(m, satisfy[1:34, 1:51], Bin)#satisfy[i, j] do we satisfy the average demand of product i on week j

@expression(m, left[1:34, 1:51], 0)
"""
left[i, j] is leftovers from item i after week j 
left[i, j] should be positive if we satisfy the week'j average demand of product i
and 0 otherwise
<=>
left[i, j] = received[i, j] + left[i, j - 1] - prod_dict[i]["avg_dem_week_j"]
0 <= left[i, j] <= satisfy[i, j] * infinity
"""

for prod_idx in 1:length(max_prod[:,1])
    prodname = max_prod[prod_idx,1]
    for week in 1:51
        left_from_last_week = 0
        if week > 1
            left_from_last_week = left[prod_idx, week - 1]
        end
        JuMP.add_to_expression!(left[prod_idx, week], received[prod_idx, week] + left_from_last_week - prod_dict[prodname][string("avg_dem_week_", week)])
        @constraint(m, left[prod_idx, week] >= 0)
        @constraint(m, left[prod_idx, week] <= satisfy[prod_idx, week] * infinity)
    end
end

@expression(m, failure[1:34, 1:51], 0)
"""
failure[i, j] is how many orders did we fail to fullfil from item i on week j
failure[i, j] should be negative if we cannot satisfy the week'j average demand of product i
and 0 otherwise
<=>
failure[i, j] = received[i, j] + left[i, j - 1] - prod_dict[i]["avg_dem_week_j"]

(1-satisfy[i, j]) * -infinity <= failure[i, j] <= 0
"""

for prod_idx in 1:length(max_prod[:,1])
    prodname = max_prod[prod_idx,1]
    for week in weeks
        left_from_last_week = 0
        if week > 1
            left_from_last_week = left[prod_idx, week - 1]
        end
        JuMP.add_to_expression!(failure[prod_idx, week], received[prod_idx, week] + left_from_last_week - prod_idx[prodname][string("avg_dem_week_", week)])
        @constraint(m, failure[prod_idx, week] <= 0)
        @constraint(m, failure[prod_idx, week] >= -(1-satisfy[prod_idx, week] * infinity)
    end
end

#don't exceed storage capacity every week
for week in 1:51
    @constraint(m, sum(left[:,week]) <= distrib_max)
