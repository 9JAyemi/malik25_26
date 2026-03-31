module fifo_controller_sva (
    input logic        ge2_free,
    input logic        ge3_free,
    input logic [1:0]  input_tm_cnt,
    input logic [3:0]  fifo_wrptr_inc
);

    // No RTL clock or reset; sample this combinational logic on the formal global clock.

    // ge3_free and cnt==3 must drive 3.
    check_ge3_free_cnt3: assert property (
        @($global_clock)
        (ge3_free && (input_tm_cnt == 2'd3)) |-> (fifo_wrptr_inc == 4'd3)
    );

    // With ge3_free low, ge2_free and cnt>=2 must drive 2.
    check_ge2_free_cnt_ge2: assert property (
        @($global_clock)
        ((!ge3_free) && ge2_free && (input_tm_cnt >= 2'd2)) |-> (fifo_wrptr_inc == 4'd2)
    );

    // With ge3_free and ge2_free low, cnt>=1 must drive 1.
    check_cnt_ge1: assert property (
        @($global_clock)
        ((!ge3_free) && (!ge2_free) && (input_tm_cnt >= 2'd1)) |-> (fifo_wrptr_inc == 4'd1)
    );

    // With no free condition and cnt>=1, 1 must still be selected.
    check_no_free_cnt_ge1: assert property (
        @($global_clock)
        ((!ge3_free) && (!ge2_free) && (input_tm_cnt >= 2'd1)) |-> (fifo_wrptr_inc == 4'd1)
    );

    // With no free condition and cnt==0, 0 must be selected.
    check_no_free_cnt0: assert property (
        @($global_clock)
        ((!ge3_free) && (!ge2_free) && (input_tm_cnt == 2'd0)) |-> (fifo_wrptr_inc == 4'd0)
    );

    // With no free condition and cnt==1, 1 must be selected.
    check_no_free_cnt1: assert property (
        @($global_clock)
        ((!ge3_free) && (!ge2_free) && (input_tm_cnt == 2'd1)) |-> (fifo_wrptr_inc == 4'd1)
    );

    // With ge3_free low and cnt==2, 2 must be selected.
    check_ge2_free_cnt2: assert property (
        @($global_clock)
        ((!ge3_free) && ge2_free && (input_tm_cnt == 2'd2)) |-> (fifo_wrptr_inc == 4'd2)
    );

    // With ge3_free low and cnt==1, 1 must be selected.
    check_ge2_free_cnt1: assert property (
        @($global_clock)
        ((!ge3_free) && ge2_free && (input_tm_cnt == 2'd1)) |-> (fifo_wrptr_inc == 4'd1)
    );

    // With ge3_free low and cnt==0, 0 must be selected.
    check_ge2_free_cnt0: assert property (
        @($global_clock)
        ((!ge3_free) && ge2_free && (input_tm_cnt == 2'd0)) |-> (fifo_wrptr_inc == 4'd0)
    );

    // With ge3_free high and cnt==2, 3 must be selected.
    check_ge3_free_cnt2: assert property (
        @($global_clock)
        (ge3_free && (input_tm_cnt == 2'd2)) |-> (fifo_wrptr_inc == 4'd3)
    );

    // With ge3_free high and cnt==1, 1 must be selected.
    check_ge3_free_cnt1: assert property (
        @($global_clock)
        (ge3_free && (input_tm_cnt == 2'd1)) |-> (fifo_wrptr_inc == 4'd1)
    );

    // With ge3_free high and cnt==0, 0 must be selected.
    check_ge3_free_cnt0: assert property (
        @($global_clock)
        (ge3_free && (input_tm_cnt == 2'd0)) |-> (fifo_wrptr_inc == 4'd0)
    );

endmodule