// SVA for booth_shift_reg
// Bind this checker to the DUT
module booth_shift_reg_sva (
  input clk,
  input reset,
  input [3:0] A,
  input [3:0] B,
  input load,
  input select,
  input [7:0] P,
  input [7:0] P_shifted,
  input [7:0] P_reg,
  input [3:0] A_reg,
  input [3:0] B_reg,
  input [2:0] count,
  input [3:0] B_shifted,
  input [1:0] shift_count
);

default clocking cb @(posedge clk); endclocking

// Helper functions model implemented RTL semantics (including sizing/truncation)
function automatic logic [7:0] nxt_P (
  input logic [2:0] cnt,
  input logic [7:0] P_r,
  input logic [3:0] A_r,
  input logic [3:0] B_r,
  input logic [3:0] Bs_r
);
  logic [8:0] t;
  nxt_P = P_r;
  unique case (cnt)
    3'b000: if (B_r[0]) begin t = {1'b0,P_r} + {5'b0,(A_r << 4)}; nxt_P = t[7:0]; end
    3'b001: if (!B_r[0] && Bs_r[0]) begin t = {1'b0,P_r} - {5'b0,(A_r << 4)}; nxt_P = t[7:0]; end
    3'b010: if (B_r[0]) begin t = {1'b0,P_r} + {5'b0,(A_r << 3)}; nxt_P = t[7:0]; end
    3'b011: if (!B_r[0] && Bs_r[0]) begin t = {1'b0,P_r} - {5'b0,(A_r << 3)}; nxt_P = t[7:0]; end
    3'b100: if (B_r[0]) begin t = {1'b0,P_r} + {5'b0,(A_r << 2)}; nxt_P = t[7:0]; end
    3'b101: if (!B_r[0] && Bs_r[0]) begin t = {1'b0,P_r} - {5'b0,(A_r << 2)}; nxt_P = t[7:0]; end
    3'b110: if (B_r[0]) begin t = {1'b0,P_r} + {5'b0,(A_r << 1)}; nxt_P = t[7:0]; end
    3'b111: if (!B_r[0] && Bs_r[0]) begin t = {1'b0,P_r} - {5'b0,(A_r << 1)}; nxt_P = t[7:0]; end
    default: nxt_P = P_r;
  endcase
endfunction

function automatic logic [3:0] nxt_Bs (
  input logic [2:0] cnt,
  input logic [3:0] Bs_r,
  input logic [3:0] B_in
);
  nxt_Bs = (cnt[0]==1'b0) ? B_in : Bs_r; // even count -> B, odd -> hold
endfunction

// Reset behavior (synchronous)
a_reset_regs: assert property (reset |=> (P_reg==8'h00 && A_reg==4'h0 && B_reg==4'h0 &&
                                          count==3'h0 && B_shifted==4'h0 && shift_count==2'h0));

// Load behavior
a_load_regs: assert property (disable iff (reset)
  load |=> (P_reg==8'h00 && A_reg==$past(A) && B_reg==$past(B) &&
            count==3'h0 && B_shifted==$past(B) && shift_count==2'h0));

// Count advance when not loading
a_count_inc: assert property (disable iff (reset)
  !load |=> count == $past(count) + 3'd1);

// A_reg/B_reg are sticky after load
a_hold_AB: assert property (disable iff (reset)
  !load |=> (A_reg==$past(A_reg) && B_reg==$past(B_reg)));

// B_shifted update rule (matches RTL truncation)
a_bshifted_upd: assert property (disable iff (reset)
  !load |=> B_shifted == nxt_Bs($past(count), $past(B_shifted), $past(B)));

// shift_count mirrors count LSB (00 on even, 01 on odd)
a_shiftcnt: assert property (disable iff (reset)
  !load |=> shift_count == {1'b0, $past(count[0])});

// P_reg update per case/conditions
a_preg_upd: assert property (disable iff (reset)
  !load |=> P_reg == nxt_P($past(count), $past(P_reg), $past(A_reg), $past(B_reg), $past(B_shifted)));

// Output mapping
a_P_mux:       assert property (select ? (P==P_reg) : (P=={P_reg[6:0],1'b0}));
a_Pshift_mux:  assert property (select ? (P_shifted=={P_reg[6:0],1'b0}) : (P_shifted=={P_reg[5:0],2'b0}));

// Basic X-check on outputs
a_no_x_out: assert property (!$isunknown({P,P_shifted}));

// Coverage

// Exercise all count states after a load pulse
c_all_counts: cover property (disable iff (reset)
  load ##1 (!load && count==3'b000) ##1 (!load && count==3'b001) ##1 (!load && count==3'b010) ##
  1 (!load && count==3'b011) ##1 (!load && count==3'b100) ##1 (!load && count==3'b101) ##
  1 (!load && count==3'b110) ##1 (!load && count==3'b111));

// Exercise add and sub paths
c_add_4:  cover property (disable iff (reset) (!load && count==3'b000 && B_reg[0]));
c_sub_4:  cover property (disable iff (reset) (!load && count==3'b001 && !B_reg[0] && B_shifted[0]));
c_add_3:  cover property (disable iff (reset) (!load && count==3'b010 && B_reg[0]));
c_sub_3:  cover property (disable iff (reset) (!load && count==3'b011 && !B_reg[0] && B_shifted[0]));
c_add_2:  cover property (disable iff (reset) (!load && count==3'b100 && B_reg[0]));
c_sub_2:  cover property (disable iff (reset) (!load && count==3'b101 && !B_reg[0] && B_shifted[0]));
c_add_1:  cover property (disable iff (reset) (!load && count==3'b110 && B_reg[0]));
c_sub_1:  cover property (disable iff (reset) (!load && count==3'b111 && !B_reg[0] && B_shifted[0]));

// Exercise select mux both ways
c_sel_toggle: cover property (select ##1 !select ##1 select);

endmodule

// Bind to DUT (connect internal regs explicitly)
bind booth_shift_reg booth_shift_reg_sva bsr_sva (
  .clk(clk),
  .reset(reset),
  .A(A),
  .B(B),
  .load(load),
  .select(select),
  .P(P),
  .P_shifted(P_shifted),
  .P_reg(P_reg),
  .A_reg(A_reg),
  .B_reg(B_reg),
  .count(count),
  .B_shifted(B_shifted),
  .shift_count(shift_count)
);