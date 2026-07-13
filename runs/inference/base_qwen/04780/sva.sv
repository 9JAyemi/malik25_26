module top_module_sva (
    input logic a,
    input logic b,
    input logic c,
    input logic d,
    output logic out_final
);
    // XOR gate output should be a ^ b
    xor_gate_output: assert property (
        @(posedge clk) disable iff (!resetn) (xor1_out == a ^ b)
    );

    // AND gate output should be (a ^ b) & (c ^ d)
    and_gate_output: assert property (
        @(posedge clk) disable iff (!resetn) (out_final == (a ^ b) & (c ^ d))
    );
endmodule