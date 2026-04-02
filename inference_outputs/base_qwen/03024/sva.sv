module mode_selector_sva (
    input wire [1:0] mode,
    input wire [3:0] in,
    output wire [3:0] out
);
    // Sequential logic is not present, so all logic is combinational.
    // No clock or reset signals are present.

    // Check that the output is correctly set based on the mode
    // Mode 00: out = {in[2:0], 1'b0}
    mode_00: assert property (
        @(posedge CLK) disable iff (!RESETn) (mode == 2'b00) |-> (out == {in[2:0], 1'b0})
    );
    // Mode 01: out = {1'b0, in[3:1]}
    mode_01: assert property (
        @(posedge CLK) disable iff (!RESETn) (mode == 2'b01) |-> (out == {1'b0, in[3:1]})
    );
    // Mode 10: out = ~in
    mode_10: assert property (
        @(posedge CLK) disable iff (!RESETn) (mode == 2'b10) |-> (out == ~in)
    );
    // Mode 11: out = in
    mode_11: assert property (
        @(posedge CLK) disable iff (!RESETn) (mode == 2'b11) |-> (out == in)
    );
    // Default mode: out = 4'b0
    default_mode: assert property (
        @(posedge CLK) disable iff (!RESETn) (mode != 2'b00 && mode != 2'b01 && mode != 2'b10 && mode != 2'b11) |-> (out == 4'b0)
    );
endmodule