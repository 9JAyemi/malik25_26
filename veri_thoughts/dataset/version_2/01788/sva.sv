module xor_8bit_sva (
    input logic clk,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [7:0] C
);
    // C must equal bitwise XOR of A and B every cycle.
    check_vector_xor: assert property (
        @(posedge clk) C == (A ^ B)
    );

    // Change in C equals XOR of changes in A and B (delta identity).
    check_delta_identity: assert property (
        @(posedge clk) 1'b1 |=> ((C ^ $past(C)) == ((A ^ $past(A)) ^ (B ^ $past(B))))
    );

    // If both inputs are stable, output must be stable too.
    check_stable_if_inputs_stable: assert property (
        @(posedge clk) 1'b1 |=> (($stable(A) && $stable(B)) |-> $stable(C))
    );

    // Each output bit equals XOR of corresponding input bits.
    genvar i;
    generate
        for (i = 0; i < 8; i++) begin : gen_bit
            // C[i] must equal A[i] ^ B[i] each cycle.
            check_bit_xor: assert property (
                @(posedge clk) C[i] == (A[i] ^ B[i])
            );
        end
    endgenerate
endmodule