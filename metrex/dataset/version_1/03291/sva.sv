// SVA for reg_read and submodules (concise, quality-focused)
// Drop into a standalone .sv file and compile with the DUT. No TB changes required.

// Top-level: equality checker correctness and basic coverage
module reg_read_top_asserts(input clk, input reset,
                            input [15:0] regValue1, regValue2,
                            input        equalValue);
  // equalValue must reflect equality of the two register read values
  a_equal_correct: assert property (@(posedge clk) equalValue == (regValue1 == regValue2));

  // Coverage: both equal and not-equal observed
  c_equal_1: cover property (@(posedge clk) equalValue);
  c_equal_0: cover property (@(posedge clk) !equalValue);
endmodule
bind reg_read reg_read_top_asserts top_asrt(.clk(clk), .reset(reset),
                                            .regValue1(regValue1), .regValue2(regValue2),
                                            .equalValue(equalValue));


// Register-file level assertions: decode, write enables, register updates, muxing, and coverage
module rf_asserts (
  input clk, input reset,
  input        write, writeR7,
  input  [2:0] readAdd1, readAdd2, writeAdd,
  input  [15:0] in, inR7,
  input  [15:0] out1, out2,
  input  [15:0] data0, data1, data2, data3, data4, data5, data6, data7,
  input  [7:0]  writeLinesInit, writeLines
);
  // Decoder should be one-hot
  a_dec_onehot: assert property (@(posedge clk) $onehot(writeLinesInit));

  // Write-line mapping: selected entry mirrors write (or writeR7 for R7); others forced 1
  genvar i;
  generate
    for (i=0; i<7; i++) begin : g_wl_0_6
      a_wl_map_sel   : assert property (@(posedge clk) (writeAdd==i)  |-> (writeLines[i] == write));
      a_wl_map_others: assert property (@(posedge clk) (writeAdd!=i) |-> (writeLines[i] == 1'b1));
    end
  endgenerate
  a_wl7_map_sel   : assert property (@(posedge clk) (writeAdd==3'd7)  |-> (writeLines[7] == writeR7));
  a_wl7_map_others: assert property (@(posedge clk) (writeAdd!=3'd7) |-> (writeLines[7] == 1'b1));

  // Reset clears all registers by the next cycle (active-low reset)
  a_reset_clears: assert property (@(posedge clk) (reset==1'b0) |=> (data0==16'h0 && data1==16'h0 && data2==16'h0 &&
                                                                    data3==16'h0 && data4==16'h0 && data5==16'h0 &&
                                                                    data6==16'h0 && data7==16'h0));

  // Writes capture on selected register when write signal is 0 (active-low write enables inside register16)
  a_w0_cap: assert property (@(posedge clk) disable iff (reset==1'b0) ((writeAdd==3'd0)&&(write==1'b0)) |=> (data0==$past(in)));
  a_w1_cap: assert property (@(posedge clk) disable iff (reset==1'b0) ((writeAdd==3'd1)&&(write==1'b0)) |=> (data1==$past(in)));
  a_w2_cap: assert property (@(posedge clk) disable iff (reset==1'b0) ((writeAdd==3'd2)&&(write==1'b0)) |=> (data2==$past(in)));
  a_w3_cap: assert property (@(posedge clk) disable iff (reset==1'b0) ((writeAdd==3'd3)&&(write==1'b0)) |=> (data3==$past(in)));
  a_w4_cap: assert property (@(posedge clk) disable iff (reset==1'b0) ((writeAdd==3'd4)&&(write==1'b0)) |=> (data4==$past(in)));
  a_w5_cap: assert property (@(posedge clk) disable iff (reset==1'b0) ((writeAdd==3'd5)&&(write==1'b0)) |=> (data5==$past(in)));
  a_w6_cap: assert property (@(posedge clk) disable iff (reset==1'b0) ((writeAdd==3'd6)&&(write==1'b0)) |=> (data6==$past(in)));
  a_w7_cap: assert property (@(posedge clk) disable iff (reset==1'b0) ((writeAdd==3'd7)&&(writeR7==1'b0)) |=> (data7==$past(inR7)));

  // Holds when not writing selected entry
  a_w0_hold: assert property (@(posedge clk) disable iff (reset==1'b0) !((writeAdd==3'd0)&&(write==1'b0)) |=> (data0==$past(data0)));
  a_w1_hold: assert property (@(posedge clk) disable iff (reset==1'b0) !((writeAdd==3'd1)&&(write==1'b0)) |=> (data1==$past(data1)));
  a_w2_hold: assert property (@(posedge clk) disable iff (reset==1'b0) !((writeAdd==3'd2)&&(write==1'b0)) |=> (data2==$past(data2)));
  a_w3_hold: assert property (@(posedge clk) disable iff (reset==1'b0) !((writeAdd==3'd3)&&(write==1'b0)) |=> (data3==$past(data3)));
  a_w4_hold: assert property (@(posedge clk) disable iff (reset==1'b0) !((writeAdd==3'd4)&&(write==1'b0)) |=> (data4==$past(data4)));
  a_w5_hold: assert property (@(posedge clk) disable iff (reset==1'b0) !((writeAdd==3'd5)&&(write==1'b0)) |=> (data5==$past(data5)));
  a_w6_hold: assert property (@(posedge clk) disable iff (reset==1'b0) !((writeAdd==3'd6)&&(write==1'b0)) |=> (data6==$past(data6)));
  a_w7_hold: assert property (@(posedge clk) disable iff (reset==1'b0) !((writeAdd==3'd7)&&(writeR7==1'b0)) |=> (data7==$past(data7)));

  // Mux correctness: out1/out2 reflect selected register
  a_mux1_d0: assert property (@(posedge clk) (readAdd1==3'd0) |-> (out1==data0));
  a_mux1_d1: assert property (@(posedge clk) (readAdd1==3'd1) |-> (out1==data1));
  a_mux1_d2: assert property (@(posedge clk) (readAdd1==3'd2) |-> (out1==data2));
  a_mux1_d3: assert property (@(posedge clk) (readAdd1==3'd3) |-> (out1==data3));
  a_mux1_d4: assert property (@(posedge clk) (readAdd1==3'd4) |-> (out1==data4));
  a_mux1_d5: assert property (@(posedge clk) (readAdd1==3'd5) |-> (out1==data5));
  a_mux1_d6: assert property (@(posedge clk) (readAdd1==3'd6) |-> (out1==data6));
  a_mux1_d7: assert property (@(posedge clk) (readAdd1==3'd7) |-> (out1==data7));

  a_mux2_d0: assert property (@(posedge clk) (readAdd2==3'd0) |-> (out2==data0));
  a_mux2_d1: assert property (@(posedge clk) (readAdd2==3'd1) |-> (out2==data1));
  a_mux2_d2: assert property (@(posedge clk) (readAdd2==3'd2) |-> (out2==data2));
  a_mux2_d3: assert property (@(posedge clk) (readAdd2==3'd3) |-> (out2==data3));
  a_mux2_d4: assert property (@(posedge clk) (readAdd2==3'd4) |-> (out2==data4));
  a_mux2_d5: assert property (@(posedge clk) (readAdd2==3'd5) |-> (out2==data5));
  a_mux2_d6: assert property (@(posedge clk) (readAdd2==3'd6) |-> (out2==data6));
  a_mux2_d7: assert property (@(posedge clk) (readAdd2==3'd7) |-> (out2==data7));

  // Coverage: write each register, read each address, same-cycle RW hazards
  c_w0: cover property (@(posedge clk) disable iff (reset==1'b0) (write==1'b0 && writeAdd==3'd0));
  c_w1: cover property (@(posedge clk) disable iff (reset==1'b0) (write==1'b0 && writeAdd==3'd1));
  c_w2: cover property (@(posedge clk) disable iff (reset==1'b0) (write==1'b0 && writeAdd==3'd2));
  c_w3: cover property (@(posedge clk) disable iff (reset==1'b0) (write==1'b0 && writeAdd==3'd3));
  c_w4: cover property (@(posedge clk) disable iff (reset==1'b0) (write==1'b0 && writeAdd==3'd4));
  c_w5: cover property (@(posedge clk) disable iff (reset==1'b0) (write==1'b0 && writeAdd==3'd5));
  c_w6: cover property (@(posedge clk) disable iff (reset==1'b0) (write==1'b0 && writeAdd==3'd6));
  c_w7: cover property (@(posedge clk) disable iff (reset==1'b0) (writeR7==1'b0 && writeAdd==3'd7));

  c_r1_each[0]: cover property (@(posedge clk) (readAdd1==3'd0));
  c_r1_each[1]: cover property (@(posedge clk) (readAdd1==3'd1));
  c_r1_each[2]: cover property (@(posedge clk) (readAdd1==3'd2));
  c_r1_each[3]: cover property (@(posedge clk) (readAdd1==3'd3));
  c_r1_each[4]: cover property (@(posedge clk) (readAdd1==3'd4));
  c_r1_each[5]: cover property (@(posedge clk) (readAdd1==3'd5));
  c_r1_each[6]: cover property (@(posedge clk) (readAdd1==3'd6));
  c_r1_each[7]: cover property (@(posedge clk) (readAdd1==3'd7));

  c_r2_each[0]: cover property (@(posedge clk) (readAdd2==3'd0));
  c_r2_each[1]: cover property (@(posedge clk) (readAdd2==3'd1));
  c_r2_each[2]: cover property (@(posedge clk) (readAdd2==3'd2));
  c_r2_each[3]: cover property (@(posedge clk) (readAdd2==3'd3));
  c_r2_each[4]: cover property (@(posedge clk) (readAdd2==3'd4));
  c_r2_each[5]: cover property (@(posedge clk) (readAdd2==3'd5));
  c_r2_each[6]: cover property (@(posedge clk) (readAdd2==3'd6));
  c_r2_each[7]: cover property (@(posedge clk) (readAdd2==3'd7));

  c_rw_hazard_r1: cover property (@(posedge clk) disable iff (reset==1'b0) (write==1'b0 && writeAdd==readAdd1));
  c_rw_hazard_r2: cover property (@(posedge clk) disable iff (reset==1'b0) (write==1'b0 && writeAdd==readAdd2));
  c_rw7_hazard_r1: cover property (@(posedge clk) disable iff (reset==1'b0) (writeR7==1'b0 && writeAdd==3'd7 && readAdd1==3'd7));
  c_rw7_hazard_r2: cover property (@(posedge clk) disable iff (reset==1'b0) (writeR7==1'b0 && writeAdd==3'd7 && readAdd2==3'd7));
endmodule
bind register_file rf_asserts rf_asrt(.clk(clk), .reset(reset),
                                      .write(write), .writeR7(writeR7),
                                      .readAdd1(readAdd1), .readAdd2(readAdd2), .writeAdd(writeAdd),
                                      .in(in), .inR7(inR7),
                                      .out1(out1), .out2(out2),
                                      .data0(data0), .data1(data1), .data2(data2), .data3(data3),
                                      .data4(data4), .data5(data5), .data6(data6), .data7(data7),
                                      .writeLinesInit(writeLinesInit), .writeLines(writeLines));


// Generic register16 semantics (applies to all instances)
module reg16_asserts(input clk, input reset, input write, input [15:0] in, input [15:0] out);
  a_rst_next_zero: assert property (@(posedge clk) (reset==1'b0) |=> (out==16'h0));
  a_load_on_wr0 : assert property (@(posedge clk) disable iff (reset==1'b0) (write==1'b0) |=> (out==$past(in)));
  a_hold_on_wr1 : assert property (@(posedge clk) disable iff (reset==1'b0) (write==1'b1) |=> (out==$past(out)));
endmodule
bind register16 reg16_asserts reg16_asrt(.clk(clk), .reset(reset), .write(write), .in(in), .out(out));