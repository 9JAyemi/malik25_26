module custom_logic_sva (
    input logic CLK,
    input logic A1,
    input logic A2,
    input logic B1_N,
    input logic Y,
    // Internal nets from RTL (optional to bind)
    input logic not_B1_N,
    input logic and0_out,
    input logic and1_out,
    input logic or0_out,
    input logic nand0_out_Y
);
    ///// Gate-level correctness /////
    // not_B1_N is the inversion of B1_N.
    check_not_B1N_inversion: assert property (
        @(posedge CLK) not_B1_N == ~B1_N
    );
    // and0_out is A1 AND A2.
    check_and0_function: assert property (
        @(posedge CLK) and0_out == (A1 & A2)
    );
    // and1_out is not_B1_N AND and0_out.
    check_and1_function: assert property (
        @(posedge CLK) and1_out == (not_B1_N & and0_out)
    );
    // or0_out is A1 OR A2.
    check_or0_function: assert property (
        @(posedge CLK) or0_out == (A1 | A2)
    );
    // nand0_out_Y is NAND of and1_out and or0_out.
    check_nand0_function: assert property (
        @(posedge CLK) nand0_out_Y == ~(and1_out & or0_out)
    );
    // Y is a buffered version of nand0_out_Y.
    check_buf_to_Y: assert property (
        @(posedge CLK) Y == nand0_out_Y
    );

    ///// Functional equivalence and implications on top-level ports /////
    // Y equals (B1_N | ~A1 | ~A2) (simplified function).
    check_simplified_function: assert property (
        @(posedge CLK) Y == (B1_N | ~A1 | ~A2)
    );
    // If B1_N is HIGH, Y must be HIGH.
    check_B1N_high_forces_Y_high: assert property (
        @(posedge CLK) (B1_N == 1'b1) |=> (Y == 1'b1)
    );
    // If A1 is LOW or A2 is LOW, Y must be HIGH.
    check_A1_or_A2_low_forces_Y_high: assert property (
        @(posedge CLK) ((A1 == 1'b0) || (A2 == 1'b0)) |=> (Y == 1'b1)
    );
    // If B1_N is LOW and A1 and A2 are HIGH, Y must be LOW.
    check_all_high_B1N_low_drives_Y_low: assert property (
        @(posedge CLK) ((B1_N == 1'b0) && (A1 == 1'b1) && (A2 == 1'b1)) |=> (Y == 1'b0)
    );
    // Y can be LOW only when B1_N is LOW and A1 and A2 are HIGH.
    check_Y_low_only_when_all_high_and_B1N_low: assert property (
        @(posedge CLK) (Y == 1'b0) |=> ((B1_N == 1'b0) && (A1 == 1'b1) && (A2 == 1'b1))
    );
endmodule