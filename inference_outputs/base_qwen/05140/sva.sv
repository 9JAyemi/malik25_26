```systemverilog
module four_bit_adder_sva (
    input logic CLK,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic CI,
    output logic [3:0] S,
    output logic CO
);
    // Full adder sum calculation
    property p_full_adder_sum;
        @(posedge CLK) disable iff (!CLK) S[0] == A[0] ^ B[0] ^ CI;
    endproperty
    assert property (p_full_adder_sum) else $error("Full adder sum calculation error");

    // Full adder carry out calculation
    property p_full_adder_carry_out;
        @(posedge CLK) disable iff (!CLK) CO == (A[0] & B[0]) | (A[0] & CI) | (B[0] & CI);
    endproperty
    assert property (p_full_adder_carry_out) else $error("Full adder carry out calculation error");

    // Propagate carry through full adders
    property p_carry_propagation;
        @(posedge CLK) disable iff (!CLK) S[1] == A[1] ^ B[1] ^ S[0];
    endproperty
    assert property (p_carry_propagation) else $error("Carry propagation error");

    property p_carry_propagation_2;
        @(posedge CLK) disable iff (!CLK) S[2] == A[2] ^ B[2] ^ S[1];
    endproperty
    assert property (p_carry_propagation_2) else $error("Carry propagation error");

    property p_carry_propagation_3;
        @(posedge CLK) disable iff (!CLK) S[3] == A[3] ^ B[3] ^ S[2];
    endproperty
    assert property (p_carry_propagation_3) else $error("Carry propagation error");

    // Final carry out
    property p_final_carry_out;
        @(posedge CLK) disable iff (!CLK) CO == (A[3] & B[3]) | (A[3] & S[2]) | (B[3] & S[2]);
    endproperty
    assert property (p_final_carry_out) else $error("Final carry out error");
endmodule
```