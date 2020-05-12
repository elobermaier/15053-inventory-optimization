using CSV, JuMP

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
#late order cost per unit for diff product types = 2x retail val
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
rush_cost = Dict(5 => 0.5, 4 => 1, 3 => 2.50, 2 => 7.50, 1 => 25)

infinity = 1000000

#copied from optimizer file
using CSV, JuMP, Cbc

products_considered = 34
demand_type = "avg_dem_week_"

m = Model(with_optimizer(Cbc.Optimizer, logLevel = 0))

@variable(m, x[1:products_considered, 1:51, 1:5] >= 0, Int) #x[i, j, k] order of item i during week j with k weeks notice

"""
The purchase plan has a cycle of k
"""
k = 0
for prod_idx in 1:products_considered
    prodname = max_prod[prod_idx,1]
    for week in k+1:51        
        #extra orders
        for week_rush in 1:5
            x[prod_idx, week, week_rush] = x[prod_idx, week - k, week_rush]
        end
    end
end

@expression(m, received[1:products_considered, 1:51], 0) #received[j, k] how many units of product j will we receive on week k
@variable(m, rate[1:products_considered, 1:51] >= 0)

for prod_idx in 1:products_considered
    prodname = max_prod[prod_idx,1]
    for week in 1:51
  
        # rushed orders
        for week_rush in 1:5
            if week >= week_rush
                JuMP.add_to_expression!(received[prod_idx, week],x[prod_idx, week - week_rush + 1, week_rush])
            end
        end

        #biweekly_replenishment
        if week % 2 == 1
            @constraint(m, rate[prod_idx, week] <= prod_dict[prodname]["biweekly_replenishment"])
        else
            @constraint(m, rate[prod_idx, week] <= 0) 
        end

        #total number of units
        received[prod_idx, week] = (received[prod_idx, week] + rate[prod_idx, week]) * prod_dict[prodname]["units_per_pallet"]                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     
    end
end

#cannot order more than production capacity
for prod_idx in 1:products_considered
    prodname = max_prod[prod_idx,1]
    for week in 1:51
        @constraint(m, sum(x[prod_idx, week, :]) <= prod_dict[prodname]["prod_capac"])
    end
end                                                                                                                                                                                                                                                         

@variable(m, left[1:products_considered, 1:51] >= 0, Int)
@variable(m, orders_sat[1:products_considered, 1:51] >= 0, Int)

for prod_idx in 1:products_considered
    prodname = max_prod[prod_idx,1]
    for week in 1:51
        if week % 2 == 1
            avg_dem = prod_dict[prodname][string(demand_type, week)]

            @constraint(m, orders_sat[prod_idx, week] <= avg_dem)

            if week > 1
                @constraint(m, left[prod_idx, week] == received[prod_idx, week] + left[prod_idx, week - 1] - orders_sat[prod_idx, week])
            else
                @constraint(m, left[prod_idx, week] == received[prod_idx, week] - orders_sat[prod_idx, week])
            end
        else
            @constraint(m, left[prod_idx, week] == left[prod_idx, week - 1] + received[prod_idx, week])
        end
    end
end

#don't exceed inventory capacity
for week in 1:51
    @constraint(m, sum(left[prod_idx, week] / prod_dict[max_prod[prod_idx,1]]["units_per_pallet"] for prod_idx in 1:products_considered) <= distrib_max)
end

@variable(m, failed_orders[1:products_considered, 1:51] >= 0)

for prod_idx in 1:products_considered
    prodname = max_prod[prod_idx,1]
    for week in 1:51
        if week % 2 == 1
            @constraint(m, failed_orders[prod_idx, week] == prod_dict[max_prod[prod_idx,1]][string(demand_type, week)] - orders_sat[prod_idx, week])
        else
            @constraint(m, failed_orders[prod_idx, week] == 0)
        end
    end
end

@expression(m, cost_of_rushed_orders, sum(x[prod_idx, week, week_rush] * rush_cost[week_rush] for prod_idx in 1:products_considered for week in 1:51 for week_rush in 1:5))

@expression(m, cost_of_failed_oders, sum(failed_orders[prod_idx, week] * late_cost[prod_dict[max_prod[prod_idx,1]]["type"]] for prod_idx in 1:products_considered for week in 1:51))

@expression(m, cost_of_inventory, sum(left[prod_idx, week] * 7 * inv_cost  for prod_idx in 1:products_considered for week in 1:51))

@objective(m, Min, cost_of_failed_oders + cost_of_rushed_orders + cost_of_inventory)
optimize!(m)

println("Objective Value: ", JuMP.objective_value(m))