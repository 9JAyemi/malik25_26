// SVA package/bind for adder4 and full_adder
// Focused, high-quality checks and concise coverage

// Assertions for full_adder cell
module full_adder_sva
(
    input logic A,
    input logic B,
    input logic Cin,
    input logic S,
    input logic Cout
);

    // No X on outputs when inputs are known
    property p_no_x_out;
        @(*) (!$isunknown({A,B,Cin})) |-> (!$isunknown({S,Cout}));
    endproperty
    assert property (p_no_x_out)
        else $error("%m: X/Z on outputs with known inputs");

    // Functional truth table
    always_comb begin
        if (!$isunknown({A,B,Cin})) begin
            assert (S    == (A ^ B ^ Cin))
                else $error("%m: S mismatch: got %0b exp %0b", S, (A^B^Cin));
            assert (Cout == ((A & B) | (A & Cin) | (B & Cin)))
                else $error("%m: Cout mismatch: got %0b exp %0b",
                            Cout, ((A & B) | (A & Cin) | (B & Cin)));
        end
    end

    // Compact coverage: hit all 8 input combinations
    always_comb begin
        cover ({A,B,Cin} == 3'b000);
        cover ({A,B,Cin} == 3'b001);
        cover ({A,B,Cin} == 3'b010);
        cover ({A,B,Cin} == 3'b011);
        cover ({A,B,Cin} == 3'b100);
        cover ({A,B,Cin} == 3'b101);
        cover ({A,B,Cin} == 3'b110);
        cover ({A,B,Cin} == 3'b111);
    end

endmodule

bind full_adder full_adder_sva fa_sva (.*);


// Assertions for parameterized ripple-carry adder
module adder4_sva #(
    parameter int WIDTH = 4
)(
    input  logic [WIDTH-1:0] A,
    input  logic [WIDTH-1:0] B,
    input  logic             Cin,
    input  logic [WIDTH-1:0] S,
    input  logic             Cout
);

    // No X on outputs when inputs are known
    property p_no_x_out;
        @(*) (!$isunknown({A,B,Cin})) |-> (!$isunknown({S,Cout}));
    endproperty
    assert property (p_no_x_out)
        else $error("%m: X/Z on outputs with known inputs");

    // End-to-end correctness: {Cout,S} == A + B + Cin
    always_comb begin
        if (!$isunknown({A,B,Cin})) begin
            logic [WIDTH:0] exp_sum;
            exp_sum = A + B + Cin;
            assert ({Cout, S} == exp_sum)
                else $error("%m: Sum mismatch: got {%0b,%0h} exp {%0b,%0h}",
                            Cout, S, exp_sum[WIDTH], exp_sum[WIDTH-1:0]);
        end
    end

    // Per-bit coverage of propagate/generate/kill and S toggle
    always_comb begin
        for (int i = 0; i < WIDTH; i++) begin
            cover (A[i] ^ B[i]);          // propagate
            cover (A[i] & B[i]);          // generate
            cover ((~A[i]) & (~B[i]));    // kill
            cover (S[i] == 0);
            cover (S[i] == 1);
        end
    end

    // Scenario coverage: key corner cases
    always_comb begin
        cover (Cin == 1'b0);
        cover (Cin == 1'b1);

        // Zero + Zero (+ Cin variants)
        cover (A == '0 && B == '0 && Cin == 1'b0 && Cout == 1'b0 && S == '0);
        cover (A == '0 && B == '0 && Cin == 1'b1 && Cout == 1'b0 && S == {{(WIDTH-1){1'b0}},1'b1});

        // All-ones + zero + Cin=1: full propagate chain
        cover (A == '1 && B == '0 && Cin == 1'b1 && Cout == 1'b1 && S == '0);

        // All-ones + all-ones + Cin=0: full generate
        cover (A == '1 && B == '1 && Cin == 1'b0 && Cout == 1'b1 && S == '0);

        // Overflow when sum wraps to zero
        cover (Cout && (S == '0));
    end

endmodule

bind adder4 adder4_sva #(.WIDTH(WIDTH)) adder_sva (.*);