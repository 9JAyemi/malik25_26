// SVA checkers for comparator_mux, comparator, and mux4to1
// Provide a free-running clk and active-high rst_n when binding/instantiating these

// Checker for comparator
module checker_comparator (
  input logic clk,
  input logic rst_n,
  input logic [1:0] in1,
  input logic [1:0] in2,
  input logic [1:0] out
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  // Functional spec: equal -> 2'b11, else per-bit greater-than
  property p_cmp_func;
    !$isunknown({in1,in2}) |->
      out == ((in1==in2) ? 2'b11 : { (in1[1] > in2[1]), (in1[0] > in2[0]) });
  endproperty
  a_cmp_func: assert property(p_cmp_func)
    else $error("comparator: functional mismatch. in1=%0b in2=%0b out=%0b", in1, in2, out);

  // Output must be known when inputs are known
  a_cmp_no_x: assert property( !$isunknown({in1,in2}) |-> !$isunknown(out) )
    else $error("comparator: X/Z on out for known inputs. in1=%0b in2=%0b out=%0b", in1, in2, out);

  // Coverage
  c_cmp_eq:   cover property ( (in1==in2) && out==2'b11 );
  c_cmp_b0gt: cover property ( (in1[0] > in2[0]) && !(in1==in2) && out==2'b01 );
  c_cmp_b1gt: cover property ( (in1[1] > in2[1]) && !(in1==in2) && out==2'b10 );
  c_cmp_both_le: cover property ( (in1[0] <= in2[0]) && (in1[1] <= in2[1]) && !(in1==in2) && out==2'b00 );
endmodule

// Checker for mux4to1
module checker_mux4to1 (
  input logic clk,
  input logic rst_n,
  input logic [1:0] in0,
  input logic [1:0] in1,
  input logic [1:0] in2,
  input logic [1:0] in3,
  input logic [1:0] sel,
  input logic [1:0] out
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  // Functional spec
  property p_mux_func;
    !$isunknown({sel,in0,in1,in2,in3}) |->
      out == ((sel==2'b00) ? in0 :
              (sel==2'b01) ? in1 :
              (sel==2'b10) ? in2 : in3);
  endproperty
  a_mux_func: assert property(p_mux_func)
    else $error("mux4to1: functional mismatch. sel=%0b out=%0b", sel, out);

  a_mux_no_x: assert property( !$isunknown({sel,in0,in1,in2,in3}) |-> !$isunknown(out) )
    else $error("mux4to1: X/Z on out for known inputs. sel=%0b out=%0b", sel, out);

  // Coverage: hit all selects
  c_sel_00: cover property (sel==2'b00);
  c_sel_01: cover property (sel==2'b01);
  c_sel_10: cover property (sel==2'b10);
  c_sel_11: cover property (sel==2'b11);
endmodule

// Checker for comparator_mux top-level selection
module checker_comparator_mux (
  input logic clk,
  input logic rst_n,
  input logic        control,
  input logic [1:0]  comp_out, // bind to internal wires of DUT
  input logic [1:0]  mux_out,  // bind to internal wires of DUT
  input logic [1:0]  out
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  // Selection correctness
  a_sel_mux:  assert property ( !$isunknown(control) && (control==1'b1) |-> out == mux_out )
    else $error("comparator_mux: control=1 but out!=mux_out. out=%0b mux_out=%0b", out, mux_out);

  a_sel_comp: assert property ( !$isunknown(control) && (control==1'b0) |-> out == comp_out )
    else $error("comparator_mux: control=0 but out!=comp_out. out=%0b comp_out=%0b", out, comp_out);

  // When control and selected source are known, out must be known
  a_top_no_x: assert property (
                 (!$isunknown(control) && control==1 && !$isunknown(mux_out)) |-> !$isunknown(out)
               )
               and
               assert property (
                 (!$isunknown(control) && control==0 && !$isunknown(comp_out)) |-> !$isunknown(out)
               )
    else $error("comparator_mux: X/Z on out with known select/source. control=%0b out=%0b", control, out);

  // Coverage: both branches and a toggle
  c_ctrl0:    cover property (control==1'b0 && out==comp_out);
  c_ctrl1:    cover property (control==1'b1 && out==mux_out);
  c_toggle01: cover property ( (control==0) ##1 (control==1) );
  c_toggle10: cover property ( (control==1) ##1 (control==0) );
endmodule

// Example bind statements (edit clk/rst nets to your environment)
// bind comparator      checker_comparator      chk_cmp   (.clk(tb_clk), .rst_n(tb_rst_n), .*);
// bind mux4to1         checker_mux4to1         chk_mux   (.clk(tb_clk), .rst_n(tb_rst_n), .*);
// bind comparator_mux  checker_comparator_mux  chk_top   (.clk(tb_clk), .rst_n(tb_rst_n),
//                                                         .control(control), .comp_out(comp_out), .mux_out(mux_out), .out(out));