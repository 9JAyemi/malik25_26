```systemverilog
module shift_register_sva (
    input logic in,
    input logic shift,
    output logic out
);
    reg [7:0] register;

    always @(posedge shift) begin
        register <= {in, register[7:1]};
    end

    always @* begin
        out = register[7];
    end

    ///// Shift register behavior /////
    // Register shifts left on each positive edge of shift signal.
    shift_left: assert property (
        @(posedge shift) $stable(register) |-> register == {in, register[7:1]}
    );

    // Output is the most significant bit of the register.
    output_msb: assert property (
        @(posedge shift) $stable(register) |-> out == register[7]
    );

    // Register is stable during the shift operation.
    register_stable: assert property (
        @(posedge shift) $stable(register) |-> register == register
    );

    // Output is stable during the shift operation.
    output_stable: assert property (
        @(posedge shift) $stable(out) |-> out == out
    );

    // Register is reset to 0 when shift is not asserted.
    register_reset: assert property (
        @(posedge shift) !shift |-> register == 8'b0
    );

    // Output is reset to 0 when shift is not asserted.
    output_reset: assert property (
        @(posedge shift) !shift |-> out == 1'b0
    );

    // Register is stable when shift is not asserted.
    register_stable_no_shift: assert property (
        @(posedge shift) !shift |-> register == register
    );

    // Output is stable when shift is not asserted.
    output_stable_no_shift: assert property (
        @(posedge shift) !shift |-> out == out
    );

    // Register is stable during the shift operation.
    register_stable_shift: assert property (
        @(posedge shift) $stable(register) |-> register == register
    );

    // Output is stable during the shift operation.
    output_stable_shift: assert property (
        @(posedge shift) $stable(out) |-> out == out
    );
endmodule
```