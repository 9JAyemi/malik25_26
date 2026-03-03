// SVA for both mux implementations. Bind this to each DUT.

module mux4to1_sva #(parameter W=4)
(
  input  logic [W-1:0] in0, in1, in2, in3,
  input  logic [1:0]   sel,
  input  logic [W-1:0] out
);

  // 4-state accurate selected data
  let sel_data = (sel==2'b00) ? in0 :
                 (sel==2'b01) ? in1 :
                 (sel==2'b10) ? in2 :
                 (sel==2'b11) ? in3 : '0;

  // Functional correctness (covers normal and X/Z on sel through default)
  a_func:    assert property (@(*)) out === sel_data;

  // Purely combinational: no latch behavior
  a_no_latch: assert property (@(*)) $stable({in0,in1,in2,in3,sel}) |-> $stable(out);

  // Coverage: each select path reached
  c_sel00: cover property (@(*)) (sel==2'b00) && (out===in0);
  c_sel01: cover property (@(*)) (sel==2'b01) && (out===in1);
  c_sel10: cover property (@(*)) (sel==2'b10) && (out===in2);
  c_sel11: cover property (@(*)) (sel==2'b11) && (out===in3);
  c_selX:  cover property (@(*)) $isunknown(sel) && (out==='0);

  // Coverage: output changes due to selected input change while sel stable
  c_in_drives_out: cover property (@(*)) !$isunknown(sel) && $stable(sel) &&
                                  !$stable(sel_data) && !$stable(out) && (out===sel_data);

  // Coverage: output changes due to sel change while inputs stable
  c_sel_switch:    cover property (@(*)) $stable({in0,in1,in2,in3}) &&
                                  !$stable(sel) && !$stable(out) && (out===sel_data);

endmodule

// Bind to both DUTs
bind mux_4to1_case mux4to1_sva #(.W(4)) mux4to1_case_sva
(
  .in0(in0), .in1(in1), .in2(in2), .in3(in3), .sel(sel), .out(out)
);

bind mux_4to1_if mux4to1_sva #(.W(4)) mux4to1_if_sva
(
  .in0(in0), .in1(in1), .in2(in2), .in3(in3), .sel(sel), .out(out)
);