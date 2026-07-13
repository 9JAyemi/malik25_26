module sp_mux_5to1_sel3_4_1_sva (
    input logic CLK,
    input logic [3:0] din1,
    input logic [3:0] din2,
    input logic [3:0] din3,
    input logic [3:0] din4,
    input logic [3:0] din5,
    input logic [2:0] din6,
    input logic [3:0] dout
);
    ///// 5-to-1 mux functionality /////
    // When sel[2] is 1, dout must equal din5.
    route_when_sel2_high: assert property (
        @(posedge CLK) disable iff (1'b0) (din6[2] == 1'b1) |-> (dout == din5)
    );

    // When sel == 3'b000, dout must equal din1.
    route_sel000_to_din1: assert property (
        @(posedge CLK) disable iff (1'b0) (din6 == 3'b000) |-> (dout == din1)
    );

    // When sel == 3'b001, dout must equal din2.
    route_sel001_to_din2: assert property (
        @(posedge CLK) disable iff (1'b0) (din6 == 3'b001) |-> (dout == din2)
    );

    // When sel == 3'b010, dout must equal din3.
    route_sel010_to_din3: assert property (
        @(posedge CLK) disable iff (1'b0) (din6 == 3'b010) |-> (dout == din3)
    );

    // When sel == 3'b011, dout must equal din4.
    route_sel011_to_din4: assert property (
        @(posedge CLK) disable iff (1'b0) (din6 == 3'b011) |-> (dout == din4)
    );

    // Direct equivalence to the nested-ternary mux structure.
    functional_equivalence: assert property (
        @(posedge CLK) disable iff (1'b0)
            dout == (din6[2] ? din5
                   : (din6[1] ? (din6[0] ? din4 : din3)
                              : (din6[0] ? din2 : din1)))
    );

    // dout always equals one of the five data inputs.
    dout_is_from_inputs: assert property (
        @(posedge CLK) disable iff (1'b0)
            (dout == din1) || (dout == din2) || (dout == din3) || (dout == din4) || (dout == din5)
    );

    // If all inputs and select are stable, dout must be stable.
    stable_when_all_stable: assert property (
        @(posedge CLK) disable iff (1'b0)
            $stable(din1) && $stable(din2) && $stable(din3) &&
            $stable(din4) && $stable(din5) && $stable(din6) |-> $stable(dout)
    );
endmodule