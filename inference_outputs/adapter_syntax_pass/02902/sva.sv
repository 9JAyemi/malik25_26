module fifo_controller_sva (
    input logic        ge2_free,
    input logic        ge3_free,
    input logic [1:0]  input_tm_cnt,
    input logic [3:0]  fifo_wrptr_inc
);

    // ge3_free and input_tm_cnt 3 select 3.
    check_ge3_selects_3: assert property (
        @($global_clock)
        (ge3_free && (input_tm_cnt == 2'd3)) |-> (fifo_wrptr_inc == 4'd3)
    );

    // ge2_free and input_tm_cnt >= 2 select 2 when ge3_free is false.
    check_ge2_selects_2: assert property (
        @($global_clock)
        ((!ge3_free) && ge2_free && (input_tm_cnt >= 2'd2)) |-> (fifo_wrptr_inc == 4'd2)
    );

    // input_tm_cnt >= 1 selects 1 when higher-priority conditions are false.
    check_tm1_selects_1: assert property (
        @($global_clock)
        ((!ge3_free) && (!ge2_free) && (input_tm_cnt >= 2'd1)) |-> (fifo_wrptr_inc == 4'd1)
    );

    // input_tm_cnt == 0 selects 0 when all conditions are false.
    check_tm0_selects_0: assert property (
        @($global_clock)
        ((!ge3_free) && (!ge2_free) && (input_tm_cnt == 2'd0)) |-> (fifo_wrptr_inc == 4'd0)
    );

    // The output is always one of the implemented encodings.
    check_output_is_valid: assert property (
        @($global_clock)
        (fifo_wrptr_inc == 4'd0) ||
        (fifo_wrptr_inc == 4'd1) ||
        (fifo_wrptr_inc == 4'd2) ||
        (fifo_wrptr_inc == 4'd3)
    );

endmodule