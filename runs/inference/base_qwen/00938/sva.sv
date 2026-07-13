module four_bit_adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    output logic [3:0] S,
    output logic Cout
);
    // No clock or reset signals present in the RTL

    // Combinational logic, so use @(posedge clk) for assertions

    // Sum calculation for each bit
    sum_0: assert property (
        @(posedge clk) $rose(S[0]) |-> (A[0] ^ B[0] ^ Cin == S[0])
    );
    sum_1: assert property (
        @(posedge clk) $rose(S[1]) |-> (A[1] ^ B[1] ^ S[0] == S[1])
    );
    sum_2: assert property (
        @(posedge clk) $rose(S[2]) |-> (A[2] ^ B[2] ^ S[1] == S[2])
    );
    sum_3: assert property (
        @(posedge clk) $rose(S[3]) |-> (A[3] ^ B[3] ^ S[2] == S[3])
    );

    // Carry calculation for each bit
    carry_0: assert property (
        @(posedge clk) $rose(Cout) |-> ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin) == Cout)
    );
    carry_1: assert property (
        @(posedge clk) $rose(carry[1]) |-> ((A[1] & B[1]) | (A[1] & carry[0]) | (B[1] & carry[0]) == carry[1])
    );
    carry_2: assert property (
        @(posedge clk) $rose(carry[2]) |-> ((A[2] & B[2]) | (A[2] & carry[1]) | (B[2] & carry[1]) == carry[2])
    );
    carry_3: assert property (
        @(posedge clk) $rose(carry[3]) |-> ((A[3] & B[3]) | (A[3] & carry[2]) | (B[3] & carry[2]) == carry[3])
    );

    // Sum and carry relationship
    sum_carry_relationship: assert property (
        @(posedge clk) $rose(S[0]) |-> (S[0] == A[0] ^ B[0] ^ Cin)
    );
    sum_carry_relationship_1: assert property (
        @(posedge clk) $rose(S[1]) |-> (S[1] == A[1] ^ B[1] ^ carry[0])
    );
    sum_carry_relationship_2: assert property (
        @(posedge clk) $rose(S[2]) |-> (S[2] == A[2] ^ B[2] ^ carry[1])
    );
    sum_carry_relationship_3: assert property (
        @(posedge clk) $rose(S[3]) |-> (S[3] == A[3] ^ B[3] ^ carry[2])
    );

    // Carry out relationship
    carry_out_relationship: assert property (
        @(posedge clk) $rose(Cout) |-> (Cout == (A[3] & B[3]) | (A[3] & carry[2]) | (B[3] & carry[2]))
    );
endmodule