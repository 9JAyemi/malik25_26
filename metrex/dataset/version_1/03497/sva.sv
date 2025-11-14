// SVA checker and bind for cla_4bit_adder
// Focus: functional correctness, internal signal consistency, concise full coverage

module cla_4bit_adder_sva
(
    input  logic [3:0] A,
    input  logic [3:0] B,
    input  logic [3:0] Y,
    // internal DUT nets
    input  logic [3:0] P,
    input  logic [3:0] G,
    input  logic [3:0] C_prop,
    input  logic [3:0] C_gen,
    input  logic [3:0] C_out
);
    // Expected values from spec
    logic [3:0] p_exp, g_exp, y_exp;
    logic c1, c2, c3, c4;
    logic inputs_known, outputs_known, overflow;

    always_comb begin
        inputs_known  = !$isunknown({A,B});
        outputs_known = !$isunknown({Y,P,G,C_prop,C_gen,C_out});

        p_exp = A ^ B;
        g_exp = A & B;

        // Carry chain (Cin=0): c1..c4 are carries into bits 1..4
        c1 = g_exp[0];
        c2 = g_exp[1] | (p_exp[1] & g_exp[0]);
        c3 = g_exp[2] | (p_exp[2] & g_exp[1]) | (p_exp[2] & p_exp[1] & g_exp[0]);
        c4 = g_exp[3] | (p_exp[3] & g_exp[2]) | (p_exp[3] & p_exp[2] & g_exp[1]) | (p_exp[3] & p_exp[2] & p_exp[1] & g_exp[0]);

        y_exp = A + B; // 4-bit sum (Cin=0), overflow truncated
        overflow = (A + B) > 4'hF;

        if (inputs_known) begin
            // No X/Z on outputs when inputs are known
            assert (outputs_known) else $error("cla_4bit_adder: X/Z on outputs for known inputs");

            // Basic propagate/generate
            assert (P === p_exp) else $error("P != A^B");
            assert (G === g_exp) else $error("G != A&B");

            // Carry generate terms
            assert (C_gen[0] === g_exp[0]) else $error("C_gen[0] mismatch");
            assert (C_gen[1] === (p_exp[1] & g_exp[0])) else $error("C_gen[1] mismatch");
            assert (C_gen[2] === ((p_exp[2] & g_exp[1]) | (p_exp[2] & p_exp[1] & g_exp[0]))) else $error("C_gen[2] mismatch");
            assert (C_gen[3] === ((p_exp[3] & g_exp[2]) | (p_exp[3] & p_exp[2] & g_exp[1]) | (p_exp[3] & p_exp[2] & p_exp[1] & g_exp[0]))) else $error("C_gen[3] mismatch");

            // Carry propagate chain should equal carries c1..c4 (OR-of terms)
            assert (C_prop[0] === c1) else $error("C_prop[0] mismatch");
            assert (C_prop[1] === c2) else $error("C_prop[1] mismatch");
            assert (C_prop[2] === c3) else $error("C_prop[2] mismatch");
            assert (C_prop[3] === c4) else $error("C_prop[3] mismatch");

            // Final carry vector and sum
            assert (C_out === {c4,c3,c2,c1}) else $error("C_out mismatch");
            assert (Y === y_exp) else $error("Y != A+B (mod 16)");
        end
    end

    // Lightweight functional coverage (sample on meaningful input changes)
    event samp;
    always_comb if (inputs_known) -> samp;

    covergroup cg @(samp);
        option.per_instance = 1;
        coverpoint A { bins all[] = {[0:15]}; }
        coverpoint B { bins all[] = {[0:15]}; }
        coverpoint Y { bins all[] = {[0:15]}; }
        // All input combinations
        AB: cross A, B;
        // Corner cases
        coverpoint overflow { bins no = {0}; bins yes = {1}; }
        coverpoint zerosum  = (Y == 4'h0);
        coverpoint fullsum  = (Y == 4'hF);
        coverpoint extremes = ((A==4'h0)||(A==4'hF)||(B==4'h0)||(B==4'hF));
    endgroup
    cg cg_i = new();

endmodule

// Bind to all instances of cla_4bit_adder, including internal nets
bind cla_4bit_adder cla_4bit_adder_sva u_cla_4bit_adder_sva (
    .A(A),
    .B(B),
    .Y(Y),
    .P(P),
    .G(G),
    .C_prop(C_prop),
    .C_gen(C_gen),
    .C_out(C_out)
);