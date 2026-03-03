// SVA for priority_encoder
module priority_encoder_sva (
  input logic        clk,
  input logic [7:0]  in,
  input logic [1:0]  pos,
  input logic [3:0]  out_sel
);

  // Outputs are known and out_sel is 0-or-onehot after update
  ap_no_x:      assert property (@(posedge clk) ##0 !$isunknown({pos,out_sel}));
  ap_onehot0:   assert property (@(posedge clk) ##0 $onehot0(out_sel));

  // out_sel priority and mapping (top half only)
  ap_os7: assert property (@(posedge clk) in[7]                    |-> ##0 (out_sel == 4'b0001));
  ap_os6: assert property (@(posedge clk) in[6] && !in[7]          |-> ##0 (out_sel == 4'b0010));
  ap_os5: assert property (@(posedge clk) in[5] && !(|in[7:6])     |-> ##0 (out_sel == 4'b0100));
  ap_os4: assert property (@(posedge clk) in[4] && !(|in[7:5])     |-> ##0 (out_sel == 4'b1000));
  ap_os0: assert property (@(posedge clk) !(|in[7:4])              |-> ##0 (out_sel == 4'b0000));

  // pos priority and (truncated) mapping as implemented
  ap_p7: assert property (@(posedge clk) in[7]                    |-> ##0 (pos == 2'b11));
  ap_p6: assert property (@(posedge clk) in[6] && !in[7]          |-> ##0 (pos == 2'b10));
  ap_p5: assert property (@(posedge clk) in[5] && !(|in[7:6])     |-> ##0 (pos == 2'b00));
  ap_p4: assert property (@(posedge clk) in[4] && !(|in[7:5])     |-> ##0 (pos == 2'b11));
  ap_p3: assert property (@(posedge clk) in[3] && !(|in[7:4])     |-> ##0 (pos == 2'b10));
  ap_p2: assert property (@(posedge clk) in[2] && !(|in[7:3])     |-> ##0 (pos == 2'b01));
  ap_p1: assert property (@(posedge clk) in[1] && !(|in[7:2])     |-> ##0 (pos == 2'b00));
  ap_p0: assert property (@(posedge clk) !(|in[7:1])              |-> ##0 (pos == 2'b00));

  // Cross-consistency: nonzero out_sel implies some top-half bit set
  ap_os_nonzero_implies_top: assert property (@(posedge clk) ##0 (out_sel != 0) |-> (|in[7:4]));

  // Coverage: each priority case and default
  cp_os7:     cover property (@(posedge clk) in[7]                    ##0 (out_sel==4'b0001 && pos==2'b11));
  cp_os6:     cover property (@(posedge clk) !in[7] && in[6]          ##0 (out_sel==4'b0010 && pos==2'b10));
  cp_os5:     cover property (@(posedge clk) !(|in[7:6]) && in[5]     ##0 (out_sel==4'b0100 && pos==2'b00));
  cp_os4:     cover property (@(posedge clk) !(|in[7:5]) && in[4]     ##0 (out_sel==4'b1000 && pos==2'b11));
  cp_p3:      cover property (@(posedge clk) !(|in[7:4]) && in[3]     ##0 (pos==2'b10));
  cp_p2:      cover property (@(posedge clk) !(|in[7:3]) && in[2]     ##0 (pos==2'b01));
  cp_p1:      cover property (@(posedge clk) !(|in[7:2]) && in[1]     ##0 (pos==2'b00));
  cp_default: cover property (@(posedge clk) !(|in[7:1])              ##0 (out_sel==4'b0000 && pos==2'b00));

  // Priority overshadow examples (multi-bit set)
  cp_prio_hi: cover property (@(posedge clk) in[7] && in[6] && in[3]  ##0 (out_sel==4'b0001 && pos==2'b11));
  cp_prio_mid:cover property (@(posedge clk) !(|in[7:6]) && in[5] && in[4] ##0 (out_sel==4'b0100 && pos==2'b00));

endmodule

bind priority_encoder priority_encoder_sva sva_i (.*);