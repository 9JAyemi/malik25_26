module hls_saturation_enqcK_sva (
    input logic CLK,
    input logic [27:0] din0,
    input logic [27:0] din1,
    input logic [27:0] din2,
    input logic [27:0] din3,
    input logic [1:0]  din4,
    input logic [27:0] dout
);
    // dout equals the nested-conditional mux function of din4 and din0..din3.
    check_mux_equation: assert property (
        @(posedge CLK) dout == (din4[1] ? (din4[0] ? din3 : din2) : (din4[0] ? din1 : din0))
    );

    // When din4==2'b00, dout equals din0.
    check_sel_00: assert property (
        @(posedge CLK) (din4 == 2'd0) |-> (dout == din0)
    );

    // When din4==2'b01, dout equals din1.
    check_sel_01: assert property (
        @(posedge CLK) (din4 == 2'd1) |-> (dout == din1)
    );

    // When din4==2'b10, dout equals din2.
    check_sel_10: assert property (
        @(posedge CLK) (din4 == 2'd2) |-> (dout == din2)
    );

    // When din4==2'b11, dout equals din3.
    check_sel_11: assert property (
        @(posedge CLK) (din4 == 2'd3) |-> (dout == din3)
    );

    // If din4[1]==0, select between din0 and din1 by din4[0].
    check_group_sel_msb0: assert property (
        @(posedge CLK) (din4[1] == 1'b0) |-> (dout == (din4[0] ? din1 : din0))
    );

    // If din4[1]==1, select between din2 and din3 by din4[0].
    check_group_sel_msb1: assert property (
        @(posedge CLK) (din4[1] == 1'b1) |-> (dout == (din4[0] ? din3 : din2))
    );
endmodule