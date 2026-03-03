// SVA checker for priority_mux
module priority_mux_sva
  #(parameter WIDTH=4)
  (
    input  logic                 clk,
    input  logic                 rst_n,
    input  logic [WIDTH-1:0]     in0, in1, in2, in3,
    input  logic                 PRI,
    input  logic [1:0]           SEL,
    input  logic [WIDTH-1:0]     out
  );

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  function automatic logic [WIDTH-1:0] golden_out(
      input logic [WIDTH-1:0] in0_i, in1_i, in2_i, in3_i,
      input logic             pri_i,
      input logic [1:0]       sel_i
  );
    if (pri_i) begin
      if (in3_i != '0)       golden_out = in3_i;
      else if (in2_i != '0)  golden_out = in2_i;
      else if (in1_i != '0)  golden_out = in1_i;
      else                   golden_out = in0_i;
    end else begin
      case (sel_i)
        2'b00: golden_out = in0_i;
        2'b01: golden_out = in1_i;
        2'b10: golden_out = in2_i;
        2'b11: golden_out = in3_i;
      endcase
    end
  endfunction

  // Functional equivalence (guarded against X/Z on inputs/outputs)
  ap_func: assert property (
    !$isunknown({PRI,SEL,in0,in1,in2,in3,out})
    |-> out == golden_out(in0,in1,in2,in3,PRI,SEL)
  );

  // PRI mode breakdown (highest-nonzero wins)
  ap_pri3: assert property (PRI && (in3 != '0)                          |-> out == in3);
  ap_pri2: assert property (PRI && (in3 == '0) && (in2 != '0)            |-> out == in2);
  ap_pri1: assert property (PRI && (in3 == '0) && (in2 == '0) && (in1!='0) |-> out == in1);
  ap_pri0: assert property (PRI && (in3 == '0) && (in2 == '0) && (in1=='0) |-> out == in0);

  // Non-PRI mux mode
  ap_mux0: assert property (!PRI && (SEL==2'b00) |-> out == in0);
  ap_mux1: assert property (!PRI && (SEL==2'b01) |-> out == in1);
  ap_mux2: assert property (!PRI && (SEL==2'b10) |-> out == in2);
  ap_mux3: assert property (!PRI && (SEL==2'b11) |-> out == in3);

  // Coverage: hit every selection path
  cp_pri3: cover property (PRI && (in3 != '0)                          && out == in3);
  cp_pri2: cover property (PRI && (in3 == '0) && (in2 != '0)            && out == in2);
  cp_pri1: cover property (PRI && (in3 == '0) && (in2 == '0) && (in1!='0) && out == in1);
  cp_pri0: cover property (PRI && (in3 == '0) && (in2 == '0) && (in1=='0) && out == in0);
  cp_mux0: cover property (!PRI && (SEL==2'b00) && out == in0);
  cp_mux1: cover property (!PRI && (SEL==2'b01) && out == in1);
  cp_mux2: cover property (!PRI && (SEL==2'b10) && out == in2);
  cp_mux3: cover property (!PRI && (SEL==2'b11) && out == in3);

endmodule

// Example bind (replace tb clock/reset with your env)
bind priority_mux priority_mux_sva #(.WIDTH(4)) u_priority_mux_sva (
  .clk(tb_clk),
  .rst_n(tb_rst_n),
  .in0(in0), .in1(in1), .in2(in2), .in3(in3),
  .PRI(PRI), .SEL(SEL), .out(out)
);