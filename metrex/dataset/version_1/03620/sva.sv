// SVA for four_to_one: out must equal reduction-OR of in, with X-aware checks and concise coverage

module four_to_one_sva (
    input logic [3:0] in,
    input logic       out
);

    // Core functional check (X-accurate, race-safe with ##0)
    property p_func;
        @(in) 1'b1 |-> ##0 (out === (|in));
    endproperty
    assert property (p_func);

    // If inputs are all known, output is known and 2-state correct
    assert property (@(in) !$isunknown(in) |-> ##0 (! $isunknown(out) && (out == (|in))));

    // If output is X, it must be due to unknown inputs and not having a definite '1' present
    assert property (@(in) $isunknown(out) |-> ##0 ($isunknown(in) && ((|in) !== 1'b1)));

    // Basic functional coverage
    cover property (@(in) ##0 (in == 4'b0000 && out === 1'b0));     // all zeros
    cover property (@(in) ##0 (in == 4'b1111 && out === 1'b1));     // all ones

    // Each single-hot input drives out=1
    genvar j;
    generate
        for (j = 0; j < 4; j++) begin : c_single_hot
            cover property (@(in) ##0 (in == (4'b0001 << j) && out === 1'b1));
        end
    endgenerate

    // Observe both edges on out
    cover property (@(posedge out) 1'b1);
    cover property (@(negedge out) 1'b1);

endmodule

// Bind into the DUT
bind four_to_one four_to_one_sva four_to_one_sva_i (.in(in), .out(out));