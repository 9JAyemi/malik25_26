// SVA for carry_select_adder_32bit
// Bind this checker to the DUT:  bind carry_select_adder_32bit carry_select_adder_32bit_sva sva_inst (.*);

module carry_select_adder_32bit_sva (
    input  logic [31:0] A,
    input  logic [31:0] B,
    input  logic        Cin,
    input  logic [31:0] S,
    input  logic        Cout
);
    // 33-bit golden result
    let exp_sum33 = ({1'b0, A} + {1'b0, B} + Cin);

    // Outputs must equal A+B+Cin (zero-time combinational)
    property p_sum_correct;
        @(A or B or Cin)
        disable iff ($isunknown({A,B,Cin}))
        ##0 {Cout, S} == exp_sum33;
    endproperty
    assert property (p_sum_correct);

    // No X/Z on outputs when inputs are known
    property p_known_outputs;
        @(A or B or Cin)
        (!$isunknown({A,B,Cin})) |-> ##0 (!$isunknown({S,Cout}));
    endproperty
    assert property (p_known_outputs);

    // Cout must be MSB of 33-bit sum
    property p_cout_bit;
        @(A or B or Cin)
        disable iff ($isunknown({A,B,Cin}))
        ##0 Cout == exp_sum33[32];
    endproperty
    assert property (p_cout_bit);

    // Basic corner coverage

    // Exercise both Cin values with zero operands
    cover property (@(A or B or Cin) ! $isunknown({A,B,Cin}) ##0 (A==32'h0 && B==32'h0 && Cin==1 && S==32'h1 && Cout==1'b0));
    cover property (@(A or B or Cin) ! $isunknown({A,B,Cin}) ##0 (A==32'h0 && B==32'h0 && Cin==0 && S==32'h0 && Cout==1'b0));

    // Observe a carry-out and a no-carry-out
    cover property (@(A or B or Cin) ! $isunknown({A,B,Cin}) ##0 (exp_sum33[32]==1 && Cout==1));
    cover property (@(A or B or Cin) ! $isunknown({A,B,Cin}) ##0 (exp_sum33[32]==0 && Cout==0));

    // Extremes
    cover property (@(A or B or Cin) ! $isunknown({A,B,Cin}) ##0
                    (A==32'hFFFF_FFFF && B==32'h0000_0001 && Cin==1 && Cout==1 && S==32'h0000_0001));
    cover property (@(A or B or Cin) ! $isunknown({A,B,Cin}) ##0
                    (A==32'hFFFF_FFFF && B==32'hFFFF_FFFF && Cin==1 && Cout==1 && S==32'hFFFF_FFFF));
endmodule

bind carry_select_adder_32bit carry_select_adder_32bit_sva sva_inst (.*);