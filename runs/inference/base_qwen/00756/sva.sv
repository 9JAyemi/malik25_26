module shift_register_sva (
    input logic [3:0] in,
    input logic shift_dir,
    input logic clk,
    output logic [3:0] out
);
    // Sequential logic for shift register
    // Shift register should shift data based on shift_dir
    shift_register_seq: assert property (
        @(posedge clk) disable iff (!clk) $rose(shift_dir) |-> (out == in)
    );
    shift_register_seq2: assert property (
        @(posedge clk) disable iff (!clk) $fell(shift_dir) |-> (out == reg4)
    );
    // Combinational logic for output
    // Output should always be the last shifted value
    shift_register_comb: assert property (
        @(posedge clk) disable iff (!clk) out == reg4
    );
endmodule