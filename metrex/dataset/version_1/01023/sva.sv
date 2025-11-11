// SVA checker for binary_adder
module binary_adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       C_in,
    input logic [3:0] S,
    input logic       C_out,
    input logic       VPWR,
    input logic       VGND,
    input logic       VPB,
    input logic       VNB
);

    // Golden 5-bit expected sum (ensure proper sizing to catch overflow)
    wire [4:0] exp = {1'b0, A} + {1'b0, B} + C_in;

    // Ripple-carry decomposition (bit-accurate)
    wire c1 = (A[0]&B[0]) | (A[0]&C_in) | (B[0]&C_in);
    wire c2 = (A[1]&B[1]) | (A[1]&c1)   | (B[1]&c1);
    wire c3 = (A[2]&B[2]) | (A[2]&c2)   | (B[2]&c2);
    wire c4 = (A[3]&B[3]) | (A[3]&c3)   | (B[3]&c3);
    wire [3:0] exp_s = { A[3]^B[3]^c3, A[2]^B[2]^c2, A[1]^B[1]^c1, A[0]^B[0]^C_in };

    // Assertions (combinational, X/Z, power, functional equivalence)
    always_comb begin
        assert (! $isunknown({A,B,C_in})) else $error("binary_adder: X/Z on inputs");
        assert (! $isunknown({S,C_out}))  else $error("binary_adder: X/Z on outputs");
        assert (VPWR===1'b1 && VPB===1'b1 && VGND===1'b0 && VNB===1'b0)
            else $error("binary_adder: illegal power pin levels");

        // Functional correctness (5-bit golden result)
        assert ({C_out,S} == exp)
            else $error("binary_adder: result mismatch exp=%0h got=%0h", exp, {C_out,S});

        // Bitwise ripple-checks (catch bit-order/carry-chain issues)
        assert (S == exp_s) else $error("binary_adder: sum bits mismatch via ripple");
        assert (C_out == c4) else $error("binary_adder: carry-out mismatch via ripple");
    end

    // Covers (key scenarios: zero, max, carry gen/propagate, cancel, boundaries)
    always_comb begin
        cover (A==4'h0 && B==4'h0 && C_in==1'b0 && S==4'h0 && C_out==1'b0);           // zero
        cover (A==4'hF && B==4'hF && C_in==1'b1 && S==4'hF && C_out==1'b1);           // max+max+cin
        cover ((A+B)    < 16 && C_in==1'b0 && C_out==1'b0);                           // no carry generate
        cover ((A+B)   >= 16 && C_in==1'b0 && C_out==1'b1);                           // carry generate
        cover ((A+B)==15 && C_in==1'b1 && S==4'h0 && C_out==1'b1);                    // carry propagate (sum=0x10)
        cover (C_in==1'b1 && A==~B && S==4'h0 && C_out==1'b1);                        // cancel then carry via Cin
        cover (C_in==1'b0 && S==4'hF && C_out==1'b0 && (A^B)==4'hF && ~(A&B)==4'hF);  // sum=0xF without carry
    end

endmodule

// Bind the checker into the DUT
bind binary_adder binary_adder_sva u_binary_adder_sva (
    .A(A), .B(B), .C_in(C_in), .S(S), .C_out(C_out),
    .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB)
);