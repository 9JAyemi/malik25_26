// SVA checker bound into top_module. Purely combinational, uses input-change eventing.
module top_module_sva (
    input  logic a, b, sel_b1, sel_b2,
    input  logic out_always, out_and, out_or, out_xor,
    input  logic [3:0] logic_gate_out
);
    // Trigger on any input change
    localparam string S = "top_module_sva";
    wire [3:0] in_vec  = {a,b,sel_b1,sel_b2};
    wire [3:0] out_vec = {out_xor,out_or,out_and,out_always};

    // Functional correctness (guard unknown inputs)
    assert property (@(a or b or sel_b1 or sel_b2)
        (!$isunknown(in_vec)) |-> (out_always == ((sel_b1 & sel_b2) ? b : a))
    ) else $error("%s: out_always != mux(a,b,sel_b1&sel_b2)", S);

    assert property (@(a or b or sel_b1 or sel_b2)
        (!$isunknown(in_vec)) |-> (out_and == (a & b & sel_b1 & sel_b2))
    ) else $error("%s: out_and mismatch", S);

    assert property (@(a or b or sel_b1 or sel_b2)
        (!$isunknown(in_vec)) |-> (out_or == (a | b | sel_b1 | sel_b2))
    ) else $error("%s: out_or mismatch", S);

    assert property (@(a or b or sel_b1 or sel_b2)
        (!$isunknown(in_vec)) |-> (out_xor == (a ^ b ^ sel_b1 ^ sel_b2))
    ) else $error("%s: out_xor mismatch", S);

    // Internal constant check
    initial assert (logic_gate_out[3] === 1'b0) else $error("%s: logic_gate_out[3] not 0 at start", S);
    assert property (@(a or b or sel_b1 or sel_b2 or logic_gate_out[3])
        logic_gate_out[3] === 1'b0
    ) else $error("%s: logic_gate_out[3] changed or is not 0", S);

    // Outputs must be known when inputs are known
    assert property (@(a or b or sel_b1 or sel_b2)
        (!$isunknown(in_vec)) |-> (!$isunknown({out_vec,logic_gate_out[3]}))
    ) else $error("%s: Unknown X/Z on outputs with known inputs", S);

    // Sanity relation: AND implies OR
    assert property (@(a or b or sel_b1 or sel_b2)
        (!$isunknown({out_and,out_or})) && (out_and == 1'b1) |-> (out_or == 1'b1)
    ) else $error("%s: and->or implication violated", S);

    // Coverage
    // Mux selects a-path and b-path
    cover property (@(a or b or sel_b1 or sel_b2)
        (!$isunknown(in_vec)) && !(sel_b1 & sel_b2) && (out_always == a)
    );
    cover property (@(a or b or sel_b1 or sel_b2)
        (!$isunknown(in_vec)) &&  (sel_b1 & sel_b2) && (out_always == b)
    );

    // Extremes: all-zeros and all-ones inputs
    cover property (@(a or b or sel_b1 or sel_b2)
        (in_vec == 4'b0000) && (out_and==0) && (out_or==0) && (out_xor==0) && (out_always==a)
    );
    cover property (@(a or b or sel_b1 or sel_b2)
        (in_vec == 4'b1111) && (out_and==1) && (out_or==1) && (out_xor==0) && (out_always==b)
    );

    // Toggle coverage on all outputs
    cover property (@(a or b or sel_b1 or sel_b2) $rose(out_always));
    cover property (@(a or b or sel_b1 or sel_b2) $fell(out_always));
    cover property (@(a or b or sel_b1 or sel_b2) $rose(out_and));
    cover property (@(a or b or sel_b1 or sel_b2) $fell(out_and));
    cover property (@(a or b or sel_b1 or sel_b2) $rose(out_or));
    cover property (@(a or b or sel_b1 or sel_b2) $fell(out_or));
    cover property (@(a or b or sel_b1 or sel_b2) $rose(out_xor));
    cover property (@(a or b or sel_b1 or sel_b2) $fell(out_xor));
endmodule

// Bind into every instance of top_module
bind top_module top_module_sva sva (
    .a(a), .b(b), .sel_b1(sel_b1), .sel_b2(sel_b2),
    .out_always(out_always), .out_and(out_and), .out_or(out_or), .out_xor(out_xor),
    .logic_gate_out(logic_gate_out)
);