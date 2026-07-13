module karnaugh_map_sva (
    input logic CLK,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic E,
    input logic F
);
    // Combinational function: F is a pure function of {A,B,C,D,E}; no reset in RTL.
    logic [4:0] X;
    logic expected_F;
    assign X = {A,B,C,D,E};

    // Expected truth table per case mapping in RTL.
    assign expected_F =
           (X == 5'b00000) ||
           (X == 5'b00111) ||
           (X == 5'b00101) ||
           (X == 5'b01101) ||
           (X == 5'b01111) ||
           (X == 5'b01110) ||
           (X == 5'b01010) ||
           (X == 5'b01011) ||
           (X == 5'b01001) ||
           (X == 5'b11000) ||
           (X == 5'b11110) ||
           (X == 5'b11111) ||
           (X == 5'b10010) ||
           (X == 5'b10011);

    ///// Functional equivalence /////
    // F equals the truth table defined by the RTL case mapping.
    check_f_equivalence: assert property (
        @(posedge CLK) F == expected_F
    );

    ///// Individual minterm checks where F must be 1 /////
    // When A..E = 00000, F must be 1.
    check_f_one_00000: assert property (
        @(posedge CLK) (X == 5'b00000) |-> (F == 1'b1)
    );
    // When A..E = 00111, F must be 1.
    check_f_one_00111: assert property (
        @(posedge CLK) (X == 5'b00111) |-> (F == 1'b1)
    );
    // When A..E = 00101, F must be 1.
    check_f_one_00101: assert property (
        @(posedge CLK) (X == 5'b00101) |-> (F == 1'b1)
    );
    // When A..E = 01101, F must be 1.
    check_f_one_01101: assert property (
        @(posedge CLK) (X == 5'b01101) |-> (F == 1'b1)
    );
    // When A..E = 01111, F must be 1.
    check_f_one_01111: assert property (
        @(posedge CLK) (X == 5'b01111) |-> (F == 1'b1)
    );
    // When A..E = 01110, F must be 1.
    check_f_one_01110: assert property (
        @(posedge CLK) (X == 5'b01110) |-> (F == 1'b1)
    );
    // When A..E = 01010, F must be 1.
    check_f_one_01010: assert property (
        @(posedge CLK) (X == 5'b01010) |-> (F == 1'b1)
    );
    // When A..E = 01011, F must be 1.
    check_f_one_01011: assert property (
        @(posedge CLK) (X == 5'b01011) |-> (F == 1'b1)
    );
    // When A..E = 01001, F must be 1.
    check_f_one_01001: assert property (
        @(posedge CLK) (X == 5'b01001) |-> (F == 1'b1)
    );
    // When A..E = 11000, F must be 1.
    check_f_one_11000: assert property (
        @(posedge CLK) (X == 5'b11000) |-> (F == 1'b1)
    );
    // When A..E = 11110, F must be 1.
    check_f_one_11110: assert property (
        @(posedge CLK) (X == 5'b11110) |-> (F == 1'b1)
    );
    // When A..E = 11111, F must be 1.
    check_f_one_11111: assert property (
        @(posedge CLK) (X == 5'b11111) |-> (F == 1'b1)
    );
    // When A..E = 10010, F must be 1.
    check_f_one_10010: assert property (
        @(posedge CLK) (X == 5'b10010) |-> (F == 1'b1)
    );
    // When A..E = 10011, F must be 1.
    check_f_one_10011: assert property (
        @(posedge CLK) (X == 5'b10011) |-> (F == 1'b1)
    );

    ///// Stability property for combinational logic /////
    // If inputs are stable, F must remain stable in the next cycle.
    check_f_stable_when_inputs_stable: assert property (
        @(posedge CLK) $stable(X) |-> $stable(F)
    );
endmodule