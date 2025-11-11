// SVA for twobitmux and eightbitmux
// Concise, high-quality checks with functional and propagation coverage.

module twobitmux_sva(input logic [1:0] in, input logic s, input logic out);

  // Functional equivalence (race-free with ##0), only when inputs are known
  property t2_func;
    @(*) (!$isunknown({s,in})) |-> ##0 (out === in[s]);
  endproperty
  a_t2_func: assert property (t2_func);

  // Output must be stable if inputs are stable
  a_t2_stable: assert property (@(*) $stable({s,in}) |-> ##0 $stable(out));

  // Coverage: both select values exercised and propagate data
  c_t2_sel0:  cover property (@(*) (s==1'b0 && !$isunknown(in[0])) ##0 (out === in[0]));
  c_t2_sel1:  cover property (@(*) (s==1'b1 && !$isunknown(in[1])) ##0 (out === in[1]));

  // Coverage: propagation on data toggle under each select
  c_t2_tog0:  cover property (@(*) (s==1'b0 && $changed(in[0])) ##0 ($changed(out) && out===in[0]));
  c_t2_tog1:  cover property (@(*) (s==1'b1 && $changed(in[1])) ##0 ($changed(out) && out===in[1]));

endmodule


module eightbitmux_sva(
  input  logic [7:0] in,
  input  logic [2:0] s,
  input  logic       out,
  // internal stage taps
  input  logic [5:0] _out
);

  // Top-level functional equivalence to ideal mux (race-free)
  property e8_func;
    @(*) (!$isunknown({s,in})) |-> ##0 (out === in[s]);
  endproperty
  a_e8_func: assert property (e8_func);

  // Internal tree correctness by stage (verifies each twobitmux connection)
  property e8_stage0;
    @(*) (!$isunknown({s[0],in})) |-> ##0
      ((s[0]==1'b0) -> (_out[0]===in[0] && _out[1]===in[2] && _out[2]===in[4] && _out[3]===in[6])) &&
      ((s[0]==1'b1) -> (_out[0]===in[1] && _out[1]===in[3] && _out[2]===in[5] && _out[3]===in[7]));
  endproperty
  a_e8_stage0: assert property (e8_stage0);

  property e8_stage1;
    @(*) (!$isunknown({s[1],_out[3:0]})) |-> ##0
      ((s[1]==1'b0) -> (_out[4]===_out[0] && _out[5]===_out[2])) &&
      ((s[1]==1'b1) -> (_out[4]===_out[1] && _out[5]===_out[3]));
  endproperty
  a_e8_stage1: assert property (e8_stage1);

  property e8_stage2;
    @(*) (!$isunknown({s[2],_out[5:4]})) |-> ##0
      ((s[2]==1'b0) -> (out===_out[4])) &&
      ((s[2]==1'b1) -> (out===_out[5]));
  endproperty
  a_e8_stage2: assert property (e8_stage2);

  // Output must be stable if inputs are stable
  a_e8_stable: assert property (@(*) $stable({s,in}) |-> ##0 $stable(out));

  // Coverage: hit all select values
  genvar i;
  generate
    for (i=0; i<8; i++) begin : gen_sel_cov
      c_e8_sel: cover property (@(*) (s==i[2:0]));
    end
  endgenerate

  // Coverage: propagation on data toggle for each selected input
  generate
    for (i=0; i<8; i++) begin : gen_tog_cov
      c_e8_tog: cover property (@(*) (s==i[2:0] && $changed(in[i])) ##0 ($changed(out) && out===in[i]));
    end
  endgenerate

endmodule


// Bind assertions to DUTs
bind twobitmux   twobitmux_sva   u_t2_sva   (.*);
bind eightbitmux eightbitmux_sva u_e8_sva   (.in(in), .s(s), .out(out), ._out(_out));