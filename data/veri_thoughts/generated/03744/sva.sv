module sp_mux_6to1_sel3_7_1_sva (
    input logic       clk,
    input logic [6:0] din1,
    input logic [6:0] din2,
    input logic [6:0] din3,
    input logic [6:0] din4,
    input logic [6:0] din5,
    input logic [6:0] din6,
    input logic [2:0] din7,
    input logic [6:0] dout
);

    // Combinational DUT sampled on an external clock; no reset is present in the RTL.

    // dout matches the implemented mux tree.
    check_dout_matches_mux_tree: assert property (
        @(posedge clk)
        dout === (
            (din7[2] == 1'b0) ?
                (
                    (din7[1] == 1'b0) ?
                        ((din7[0] == 1'b0) ? din1 : din2) :
                        ((din7[0] == 1'b0) ? din3 : din4)
                ) :
                ((din7[0] == 1'b0) ? din5 : din6)
        )
    );

    // Select 000 routes din1.
    check_sel_000_routes_din1: assert property (
        @(posedge clk) (din7 == 3'b000) |-> (dout === din1)
    );

    // Select 001 routes din2.
    check_sel_001_routes_din2: assert property (
        @(posedge clk) (din7 == 3'b001) |-> (dout === din2)
    );

    // Select 010 routes din3.
    check_sel_010_routes_din3: assert property (
        @(posedge clk) (din7 == 3'b010) |-> (dout === din3)
    );

    // Select 011 routes din4.
    check_sel_011_routes_din4: assert property (
        @(posedge clk) (din7 == 3'b011) |-> (dout === din4)
    );

    // Selects 100 and 110 both route din5.
    check_sel_100_110_route_din5: assert property (
        @(posedge clk) ((din7 == 3'b100) || (din7 == 3'b110)) |-> (dout === din5)
    );

    // Selects 101 and 111 both route din6.
    check_sel_101_111_route_din6: assert property (
        @(posedge clk) ((din7 == 3'b101) || (din7 == 3'b111)) |-> (dout === din6)
    );

endmodule