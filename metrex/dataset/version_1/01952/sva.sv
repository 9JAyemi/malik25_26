// SystemVerilog Assertions for top_module and submodules.
// Bind these into the DUT; concise but high-value checks and covers.

module mux_3to4_sva (
    input logic clk,
    input logic reset,
    input logic a, b, c,
    input logic w, x, y, z,
    input logic [31:0] mux_out
);
    default clocking cb @(posedge clk); endclocking

    bit past_valid;
    initial past_valid = 1'b0;
    always @(posedge clk) past_valid <= 1'b1;

    // During reset outputs are 0
    a_reset_zeros: assert property (reset |-> (mux_out == 32'h0 && {w,x,y,z} == 4'b0000));

    // No X/Z on outputs out of reset
    a_no_xz: assert property (disable iff (reset) !$isunknown({w,x,y,z,mux_out}));

    // One-cycle pipeline mapping from {a,b,c} to zero-extended value
    a_pipeline_val: assert property (disable iff (reset)
                                     past_valid && !$past(reset)
                                     |-> mux_out == {29'b0, $past({a,b,c})});

    // Bit-slice mapping to {w,x,y,z}
    a_bitmap: assert property ({w,x,y,z} == mux_out[3:0]);

    // Since mux_out is 0..7, bit3 must always be 0
    a_w_is_zero: assert property (w == 1'b0);

    // Functional coverage: exercise all 8 mux outputs
    c_val_000: cover property (disable iff (reset) mux_out == 32'h0);
    c_val_001: cover property (disable iff (reset) mux_out == 32'h1);
    c_val_010: cover property (disable iff (reset) mux_out == 32'h2);
    c_val_011: cover property (disable iff (reset) mux_out == 32'h3);
    c_val_100: cover property (disable iff (reset) mux_out == 32'h4);
    c_val_101: cover property (disable iff (reset) mux_out == 32'h5);
    c_val_110: cover property (disable iff (reset) mux_out == 32'h6);
    c_val_111: cover property (disable iff (reset) mux_out == 32'h7);

endmodule


module byte_reversal_sva (
    input logic clk,
    input logic reset,
    input logic [31:0] in,
    input logic [31:0] out
);
    default clocking cb @(posedge clk); endclocking

    function automatic logic [31:0] swap32(input logic [31:0] v);
        swap32 = {v[7:0], v[15:8], v[23:16], v[31:24]};
    endfunction

    bit past_valid;
    initial past_valid = 1'b0;
    always @(posedge clk) past_valid <= 1'b1;

    // During reset output is 0
    a_reset_zeros: assert property (reset |-> out == 32'h0);

    // No X/Z on output out of reset
    a_no_xz: assert property (disable iff (reset) !$isunknown(out));

    // One-cycle pipeline: output is byte-swapped previous input
    a_pipeline_swap: assert property (disable iff (reset)
                                      past_valid && !$past(reset)
                                      |-> out == swap32($past(in)));

    // Coverage: observe a non-trivial swap
    c_nontrivial_swap: cover property (disable iff (reset)
                                       past_valid && !$past(reset) &&
                                       $past(in) != 32'h0 &&
                                       out == swap32($past(in)) &&
                                       out != $past(in));

endmodule


module top_module_sva (
    input logic clk,
    input logic reset,
    // tap top-level signals/wires
    input logic a, b, c,
    input logic [31:0] in,
    input logic w, x, y, z,
    input logic [31:0] mux_out,
    input logic [31:0] reverse_out,
    input logic [31:0] out
);
    default clocking cb @(posedge clk); endclocking

    // Top-level integration: XOR relation must always hold
    a_xor_integrates: assert property (out == (mux_out ^ reverse_out));

    // No X/Z on final output out of reset
    a_no_xz_out: assert property (disable iff (reset) !$isunknown(out));

    // Coverage: non-zero XOR result observed; reset sequence observed
    c_xor_nonzero: cover property (disable iff (reset) (mux_out ^ reverse_out) != 32'h0 && out == (mux_out ^ reverse_out));
    c_reset_cycle: cover property (reset ##1 !reset);

endmodule


// Bind checkers to DUT
bind mux_3to4      mux_3to4_sva    u_mux_3to4_sva   (.clk(clk), .reset(reset), .a(a), .b(b), .c(c), .w(w), .x(x), .y(y), .z(z), .mux_out(mux_out));
bind byte_reversal byte_reversal_sva u_byte_rev_sva (.clk(clk), .reset(reset), .in(in), .out(out));
bind top_module    top_module_sva   u_top_sva       (.clk(clk), .reset(reset), .a(a), .b(b), .c(c), .in(in), .w(w), .x(x), .y(y), .z(z), .mux_out(mux_out), .reverse_out(reverse_out), .out(out));