// SVA for top_module and absolute_value
// Bind these into the DUTs

module top_module_sva (
    input  signed [15:0] in1,
    input  signed [15:0] in2,
    input  signed [15:0] sum_out,
    input         [15:0] absolute_in,
    input         [15:0] max_out
);
    // Derived combs matching DUT intent
    wire [2:0]  pri    = {sum_out[15], absolute_in[15], (sum_out[14:0] > absolute_in[14:0])};
    wire [15:0] decode = 16'h0001 << pri;

    // Arithmetic correctness
    assert property (@(in1 or in2 or sum_out)
        $signed(sum_out) == $signed(in1) + $signed(in2));

    // Decode correctness
    assert property (@(sum_out or absolute_in or max_out)
        max_out == decode);

    // One-hot output in low byte only
    assert property (@(max_out)
        (max_out[15:8] == 8'h00) && $onehot(max_out[7:0]));

    // No X/Z on outputs when driving inputs are known
    assert property (@(sum_out)
        !$isunknown({in1,in2}) |-> !$isunknown(sum_out));
    assert property (@(max_out)
        !$isunknown({sum_out,absolute_in}) |-> !$isunknown(max_out));

    // Functional coverage: all 8 decode cases + input bit conditions
    genvar i;
    generate
        for (i=0;i<8;i++) begin : g_cov
            cover property (@(sum_out or absolute_in)
                pri == i[2:0] && max_out == (16'h0001 << i));
        end
    endgenerate
    cover property (@(sum_out) sum_out[15]==0);
    cover property (@(sum_out) sum_out[15]==1);
    cover property (@(absolute_in) absolute_in[15]==0);
    cover property (@(absolute_in) absolute_in[15]==1);
    cover property (@(sum_out or absolute_in) (sum_out[14:0] >  absolute_in[14:0]));
    cover property (@(sum_out or absolute_in) (sum_out[14:0] <= absolute_in[14:0]));
endmodule

bind top_module top_module_sva u_top_module_sva (.*);


module absolute_value_sva (
    input  signed [15:0] in,
    input         [15:0] out
);
    // Exact abs() behavior, including -32768 corner
    assert property (@(in or out)
        out == (in[15] ? (~in + 16'd1) : $unsigned(in)));

    // For all negatives except -32768, MSB of out must be 0
    assert property (@(in or out)
        (in != -16'sd32768 && in < 0) |-> (out[15] == 1'b0));

    // No X/Z on output when input known
    assert property (@(out)
        !$isunknown(in) |-> !$isunknown(out));

    // Coverage: negative, non-negative, and min-int corner
    cover property (@(in) in < 0);
    cover property (@(in) in >= 0);
    cover property (@(in) in == -16'sd32768);
endmodule

bind absolute_value absolute_value_sva u_absolute_value_sva (.*);