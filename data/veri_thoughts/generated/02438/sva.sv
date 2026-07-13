module top_module_sva (
    input logic clk,
    input logic [7:0] d,
    input logic [2:0] select,
    input logic [7:0] q
);

    ///// Selection-to-output mapping /////
    // When select == 0, q reflects current d.
    check_select0_direct: assert property (
        @(posedge clk) (select == 3'd0) |-> (q == d)
    );

    // When select == 1, q reflects d from 1 cycle ago.
    check_select1_delay1: assert property (
        @(posedge clk) (select == 3'd1) |-> (q == $past(d,1))
    );

    // When select == 2, q reflects d from 2 cycles ago.
    check_select2_delay2: assert property (
        @(posedge clk) (select == 3'd2) |-> (q == $past(d,2))
    );

    // When select == 3, q reflects d from 3 cycles ago.
    check_select3_delay3: assert property (
        @(posedge clk) (select == 3'd3) |-> (q == $past(d,3))
    );

    // When select == 4, q reflects d from 4 cycles ago.
    check_select4_delay4: assert property (
        @(posedge clk) (select == 3'd4) |-> (q == $past(d,4))
    );

    // When select == 5, q reflects d from 5 cycles ago.
    check_select5_delay5: assert property (
        @(posedge clk) (select == 3'd5) |-> (q == $past(d,5))
    );

    // When select == 6, q reflects d from 6 cycles ago.
    check_select6_delay6: assert property (
        @(posedge clk) (select == 3'd6) |-> (q == $past(d,6))
    );

    // When select == 7, q reflects d from 7 cycles ago.
    check_select7_delay7: assert property (
        @(posedge clk) (select == 3'd7) |-> (q == $past(d,7))
    );

    ///// Output consistency /////
    // q must equal one of the last 8 samples of d.
    check_q_within_last8_d: assert property (
        @(posedge clk)
            (q == d) ||
            (q == $past(d,1)) ||
            (q == $past(d,2)) ||
            (q == $past(d,3)) ||
            (q == $past(d,4)) ||
            (q == $past(d,5)) ||
            (q == $past(d,6)) ||
            (q == $past(d,7))
    );

    // If select increments by 1, q holds its previous value.
    check_q_holds_on_select_inc: assert property (
        @(posedge clk) (select == ($past(select) + 3'd1)) |-> (q == $past(q))
    );

    // If the last 8 d samples are identical, q equals d regardless of select.
    check_q_equals_d_when_d_steady_8: assert property (
        @(posedge clk)
            ((d == $past(d,1)) && (d == $past(d,2)) && (d == $past(d,3)) &&
             (d == $past(d,4)) && (d == $past(d,5)) && (d == $past(d,6)) &&
             (d == $past(d,7))) |-> (q == d)
    );

endmodule