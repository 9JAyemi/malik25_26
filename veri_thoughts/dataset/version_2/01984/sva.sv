module binary_ones_complement_sva (
    input  logic        CLK,
    input  logic [3:0]  B,
    input  logic [3:0]  C
);

    // Output is always the bitwise complement of input.
    check_complement_bus: assert property (
        @(posedge CLK) disable iff ($initstate) C == ~B
    );

    // If input holds its value, output holds its value.
    check_stable_if_input_stable: assert property (
        @(posedge CLK) disable iff ($initstate) (B == $past(B)) |-> (C == $past(C))
    );

    // Output does not change unless input changes.
    check_output_change_requires_input_change: assert property (
        @(posedge CLK) disable iff ($initstate) $changed(C) |-> $changed(B)
    );

    // Rising input bit causes falling output bit (inverse relation).
    check_inverse_edge_b0_rise: assert property (
        @(posedge CLK) disable iff ($initstate) $rose(B[0]) |-> $fell(C[0])
    );
    check_inverse_edge_b1_rise: assert property (
        @(posedge CLK) disable iff ($initstate) $rose(B[1]) |-> $fell(C[1])
    );
    check_inverse_edge_b2_rise: assert property (
        @(posedge CLK) disable iff ($initstate) $rose(B[2]) |-> $fell(C[2])
    );
    check_inverse_edge_b3_rise: assert property (
        @(posedge CLK) disable iff ($initstate) $rose(B[3]) |-> $fell(C[3])
    );

    // Falling input bit causes rising output bit (inverse relation).
    check_inverse_edge_b0_fall: assert property (
        @(posedge CLK) disable iff ($initstate) $fell(B[0]) |-> $rose(C[0])
    );
    check_inverse_edge_b1_fall: assert property (
        @(posedge CLK) disable iff ($initstate) $fell(B[1]) |-> $rose(C[1])
    );
    check_inverse_edge_b2_fall: assert property (
        @(posedge CLK) disable iff ($initstate) $fell(B[2]) |-> $rose(C[2])
    );
    check_inverse_edge_b3_fall: assert property (
        @(posedge CLK) disable iff ($initstate) $fell(B[3]) |-> $rose(C[3])
    );

endmodule