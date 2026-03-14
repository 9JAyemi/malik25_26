module Add_Subt_sva (
    input logic        clk,
    input logic        rst,          // active-high synchronous reset
    input logic        load_i,
    input logic        Add_Sub_op_i, // 1: subtract, 0: add
    input logic [25:0] Data_A_i,
    input logic [25:0] PreData_B_i,
    input logic [25:0] Data_Result_o,
    input logic        FSM_C_o
);
    // One cycle after reset was asserted, outputs must be zero.
    reset_clears_outputs_next: assert property (
        @(posedge clk) disable iff (rst) $past(rst) |-> (Data_Result_o == 26'd0) && (FSM_C_o == 1'b0)
    );

    // If both reset and load were high, reset has priority and outputs go to zero next cycle.
    reset_has_priority_over_load: assert property (
        @(posedge clk) disable iff (rst) $past(rst && load_i) |-> (Data_Result_o == 26'd0) && (FSM_C_o == 1'b0)
    );

    // With load and Add_Sub_op_i==0, next-cycle outputs equal 27-bit sum of inputs.
    load_updates_sum_next: assert property (
        @(posedge clk) disable iff (rst)
            (load_i && !Add_Sub_op_i)
            |=> ({FSM_C_o, Data_Result_o} == ({1'b0, $past(Data_A_i)} + {1'b0, $past(PreData_B_i)}))
    );

    // With load and Add_Sub_op_i==1, next-cycle outputs equal 27-bit difference of inputs.
    load_updates_sub_next: assert property (
        @(posedge clk) disable iff (rst)
            (load_i && Add_Sub_op_i)
            |=> ({FSM_C_o, Data_Result_o} == ({1'b0, $past(Data_A_i)} - {1'b0, $past(PreData_B_i)}))
    );

    // When load is low, outputs hold their previous values.
    hold_without_load: assert property (
        @(posedge clk) disable iff (rst)
            (!load_i) |=> ({FSM_C_o, Data_Result_o} == $past({FSM_C_o, Data_Result_o}))
    );

    // Outputs may change only on cycles following a load (ignoring reset cycles).
    change_only_after_load: assert property (
        @(posedge clk) disable iff (rst)
            $changed({FSM_C_o, Data_Result_o}) |-> $past(load_i)
    );

    // On load with addition, overflow flag equals MSB of the 27-bit sum next cycle.
    fsm_c_matches_carry_on_sum: assert property (
        @(posedge clk) disable iff (rst)
            (load_i && !Add_Sub_op_i)
            |=> (FSM_C_o == (({1'b0, $past(Data_A_i)} + {1'b0, $past(PreData_B_i)})[26]))
    );

    // On load with subtraction, overflow flag equals MSB of the 27-bit difference next cycle.
    fsm_c_matches_borrow_on_sub: assert property (
        @(posedge clk) disable iff (rst)
            (load_i && Add_Sub_op_i)
            |=> (FSM_C_o == (({1'b0, $past(Data_A_i)} - {1'b0, $past(PreData_B_i)})[26]))
    );
endmodule