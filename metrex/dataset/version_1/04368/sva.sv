// SVA for adder: concise, high-quality checks and targeted coverage

package adder_sva_pkg;
  checker adder_sva(input logic clk,
                    input logic [7:0] A, B,
                    input logic [7:0] S,
                    input logic       C_out);
    default clocking @(posedge clk); endclocking

    // Functional correctness (full 9-bit sum)
    a_sum:    assert property( !$isunknown({A,B}) |-> ({C_out,S} == (A + B)) );

    // X-propagation sanity: known inputs imply known outputs
    a_known:  assert property( !$isunknown({A,B}) |-> !$isunknown({S,C_out}) );

    // Combinational stability: stable inputs => stable outputs
    a_stable: assert property( !$isunknown({A,B}) && $stable({A,B}) |-> $stable({S,C_out}) );

    // Targeted functional coverage
    c_cout0:  cover property( !$isunknown({A,B}) && C_out==0 );
    c_cout1:  cover property( !$isunknown({A,B}) && C_out==1 );
    c_min:    cover property( A==8'h00 && B==8'h00 && S==8'h00 && C_out==0 );
    c_max:    cover property( A==8'hFF && B==8'hFF && S==8'hFE && C_out==1 );
    c_wrap:   cover property( A==8'hFF && B==8'h01 && S==8'h00 && C_out==1 );
    c_msb:    cover property( A==8'h80 && B==8'h80 && S==8'h00 && C_out==1 );
  endchecker
endpackage

// Bind (provide a testbench clock 'tb_clk')
import adder_sva_pkg::*;
bind adder adder_sva sva(.clk(tb_clk), .A(A), .B(B), .S(S), .C_out(C_out));

/* Optional: if you prefer clockless immediate assertions in pure combinational sims:
module adder_immediate_sva (input [7:0] A,B,S, input C_out);
  always_comb if (!$isunknown({A,B})) begin
    assert ({C_out,S} == A + B);
    assert (!$isunknown({S,C_out}));
  end
endmodule
bind adder adder_immediate_sva imm(.A(A),.B(B),.S(S),.C_out(C_out));
*/