module top_module_sva (
    input logic CLK,
    input logic [15:0] D,
    input logic [15:0] V,
    input logic equal,
    input logic greater,
    input logic [3:0] Q_out
);

    ///// Magnitude comparator behavior /////
    // equal reflects D[3:0] == V[3:0].
    check_equal_definition: assert property (
        @(posedge CLK) equal == (D[3:0] == V[3:0])
    );
    // greater reflects D[3:0] > V[3:0].
    check_greater_definition: assert property (
        @(posedge CLK) greater == (D[3:0] > V[3:0])
    );
    // equal implies not greater.
    check_equal_implies_not_greater: assert property (
        @(posedge CLK) equal |-> !greater
    );
    // greater implies not equal.
    check_greater_implies_not_equal: assert property (
        @(posedge CLK) greater |-> !equal
    );
    // equal and greater are mutually exclusive.
    check_equal_greater_mutex: assert property (
        @(posedge CLK) !(equal && greater)
    );

    ///// functional_module output selection /////
    // When V!=0 and greater, Q_out equals high nibble of (D/V).
    check_qout_high_when_greater: assert property (
        @(posedge CLK) (V != 16'd0 && greater) |-> (Q_out == (D / V)[15:12])
    );
    // When V!=0 and not greater, Q_out equals low nibble of (D/V).
    check_qout_low_when_not_greater: assert property (
        @(posedge CLK) (V != 16'd0 && !greater) |-> (Q_out == (D / V)[3:0])
    );
    // When V!=0 and D[3:0]==V[3:0], Q_out equals low nibble of (D/V).
    check_qout_when_equal_low: assert property (
        @(posedge CLK) (V != 16'd0 && (D[3:0] == V[3:0])) |-> (Q_out == (D / V)[3:0])
    );
    // When V!=0, Q_out is either high or low nibble of (D/V).
    check_qout_selects_valid_nibble: assert property (
        @(posedge CLK) (V != 16'd0) |-> ((Q_out == (D / V)[15:12]) || (Q_out == (D / V)[3:0]))
    );

    ///// Additional comparator relations /////
    // If D[3:0] < V[3:0], then both equal and greater are 0.
    check_less_implies_flags_zero: assert property (
        @(posedge CLK) (D[3:0] < V[3:0]) |-> (!equal && !greater)
    );

endmodule