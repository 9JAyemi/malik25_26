module sp_mux_8to1_sel4_7_1_sva (
    input logic       clk,
    input logic [6:0] din1,
    input logic [6:0] din2,
    input logic [6:0] din3,
    input logic [6:0] din4,
    input logic [6:0] din5,
    input logic [6:0] din6,
    input logic [6:0] din7,
    input logic [6:0] din8,
    input logic [3:0] din9,
    input logic [6:0] dout
);

    // dout must match the mux function driven by din9[2:0].
    check_dout_matches_mux_function: assert property (
        @(posedge clk)
        dout == ((din9[2] == 1'b0) ?
                    ((din9[1] == 1'b0) ?
                        ((din9[0] == 1'b0) ? din1 : din2) :
                        ((din9[0] == 1'b0) ? din3 : din4)) :
                    ((din9[1] == 1'b0) ?
                        ((din9[0] == 1'b0) ? din5 : din6) :
                        ((din9[0] == 1'b0) ? din7 : din8)))
    );

    // Select value 000 routes din1 to dout.
    check_sel_000_routes_din1: assert property (
        @(posedge clk)
        (din9[2:0] == 3'b000) |-> (dout == din1)
    );

    // Select value 001 routes din2 to dout.
    check_sel_001_routes_din2: assert property (
        @(posedge clk)
        (din9[2:0] == 3'b001) |-> (dout == din2)
    );

    // Select value 010 routes din3 to dout.
    check_sel_010_routes_din3: assert property (
        @(posedge clk)
        (din9[2:0] == 3'b010) |-> (dout == din3)
    );

    // Select value 011 routes din4 to dout.
    check_sel_011_routes_din4: assert property (
        @(posedge clk)
        (din9[2:0] == 3'b011) |-> (dout == din4)
    );

    // Select value 100 routes din5 to dout.
    check_sel_100_routes_din5: assert property (
        @(posedge clk)
        (din9[2:0] == 3'b100) |-> (dout == din5)
    );

    // Select value 101 routes din6 to dout.
    check_sel_101_routes_din6: assert property (
        @(posedge clk)
        (din9[2:0] == 3'b101) |-> (dout == din6)
    );

    // Select value 110 routes din7 to dout.
    check_sel_110_routes_din7: assert property (
        @(posedge clk)
        (din9[2:0] == 3'b110) |-> (dout == din7)
    );

    // Select value 111 routes din8 to dout.
    check_sel_111_routes_din8: assert property (
        @(posedge clk)
        (din9[2:0] == 3'b111) |-> (dout == din8)
    );

endmodule