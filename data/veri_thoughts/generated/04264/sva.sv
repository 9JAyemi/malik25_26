module clock_multiplexer_4_assertions (
    input logic [3:0] clk,
    input logic [1:0] ctrl,
    input logic out_clk
);

    // ctrl=0 selects clk[0].
    check_select_clk0: assert property (
        @(posedge clk[0] or posedge clk[1] or posedge clk[2] or posedge clk[3])
        (ctrl == 2'd0) |-> (out_clk == clk[0])
    );

    // ctrl=1 selects clk[1].
    check_select_clk1: assert property (
        @(posedge clk[0] or posedge clk[1] or posedge clk[2] or posedge clk[3])
        (ctrl == 2'd1) |-> (out_clk == clk[1])
    );

    // ctrl=2 selects clk[2].
    check_select_clk2: assert property (
        @(posedge clk[0] or posedge clk[1] or posedge clk[2] or posedge clk[3])
        (ctrl == 2'd2) |-> (out_clk == clk[2])
    );

    // ctrl=3 selects clk[3].
    check_select_clk3: assert property (
        @(posedge clk[0] or posedge clk[1] or posedge clk[2] or posedge clk[3])
        (ctrl == 2'd3) |-> (out_clk == clk[3])
    );

endmodule

module clock_multiplexer_8_assertions (
    input logic [7:0] clk,
    input logic [2:0] ctrl,
    input logic out_clk
);

    // ctrl=0 selects clk[0].
    check_select_clk0: assert property (
        @(posedge clk[0] or posedge clk[1] or posedge clk[2] or posedge clk[3] or posedge clk[4] or posedge clk[5] or posedge clk[6] or posedge clk[7])
        (ctrl == 3'd0) |-> (out_clk == clk[0])
    );

    // ctrl=1 selects clk[1].
    check_select_clk1: assert property (
        @(posedge clk[0] or posedge clk[1] or posedge clk[2] or posedge clk[3] or posedge clk[4] or posedge clk[5] or posedge clk[6] or posedge clk[7])
        (ctrl == 3'd1) |-> (out_clk == clk[1])
    );

    // ctrl=2 selects clk[2].
    check_select_clk2: assert property (
        @(posedge clk[0] or posedge clk[1] or posedge clk[2] or posedge clk[3] or posedge clk[4] or posedge clk[5] or posedge clk[6] or posedge clk[7])
        (ctrl == 3'd2) |-> (out_clk == clk[2])
    );

    // ctrl=3 selects clk[3].
    check_select_clk3: assert property (
        @(posedge clk[0] or posedge clk[1] or posedge clk[2] or posedge clk[3] or posedge clk[4] or posedge clk[5] or posedge clk[6] or posedge clk[7])
        (ctrl == 3'd3) |-> (out_clk == clk[3])
    );

    // ctrl=4 selects clk[4].
    check_select_clk4: assert property (
        @(posedge clk[0] or posedge clk[1] or posedge clk[2] or posedge clk[3] or posedge clk[4] or posedge clk[5] or posedge clk[6] or posedge clk[7])
        (ctrl == 3'd4) |-> (out_clk == clk[4])
    );

    // ctrl=5 selects clk[5].
    check_select_clk5: assert property (
        @(posedge clk[0] or posedge clk[1] or posedge clk[2] or posedge clk[3] or posedge clk[4] or posedge clk[5] or posedge clk[6] or posedge clk[7])
        (ctrl == 3'd5) |-> (out_clk == clk[5])
    );

    // ctrl=6 selects clk[6].
    check_select_clk6: assert property (
        @(posedge clk[0] or posedge clk[1] or posedge clk[2] or posedge clk[3] or posedge clk[4] or posedge clk[5] or posedge clk[6] or posedge clk[7])
        (ctrl == 3'd6) |-> (out_clk == clk[6])
    );

    // ctrl=7 selects clk[7].
    check_select_clk7: assert property (
        @(posedge clk[0] or posedge clk[1] or posedge clk[2] or posedge clk[3] or posedge clk[4] or posedge clk[5] or posedge clk[6] or posedge clk[7])
        (ctrl == 3'd7) |-> (out_clk == clk[7])
    );

endmodule