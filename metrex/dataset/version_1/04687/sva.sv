// SVA checker for mux_priority_encoder_decoder
// Bind this checker to the DUT to verify combinational behavior, priority, and selection.
// Quality-focused: concise, complete functional checking plus targeted coverage.

module mux_priority_encoder_decoder_sva
(
  input  logic [2:0] sel,
  input  logic [3:0] data0, data1, data2, data3, data4, data5,
  input  logic [3:0] out,

  // Internal observability (bind to DUT internals)
  input  logic [3:0] mux_out [5:0],
  input  logic [2:0] highest_priority,
  input  logic [2:0] selected_input
);

  // Event to sample on any combinational change
  event comb_ev;
  always @* -> comb_ev;

  // Expected combinational mapping
  function automatic logic [3:0] exp_mux (int idx);
    unique case (sel)
      3'b000: exp_mux = (idx==0)?data0 : (idx==1)?data1 : (idx==2)?data2 :
                         (idx==3)?data3 : (idx==4)?data4 : (idx==5)?data5 : 4'b0;
      3'b001: exp_mux = (idx==0)?data1 : (idx==1)?data0 : (idx==2)?data2 :
                         (idx==3)?data3 : (idx==4)?data4 : (idx==5)?data5 : 4'b0;
      3'b010: exp_mux = (idx==0)?data2 : (idx==1)?data0 : (idx==2)?data1 :
                         (idx==3)?data3 : (idx==4)?data4 : (idx==5)?data5 : 4'b0;
      3'b011: exp_mux = (idx==0)?data3 : (idx==1)?data0 : (idx==2)?data1 :
                         (idx==3)?data2 : (idx==4)?data4 : (idx==5)?data5 : 4'b0;
      3'b100: exp_mux = (idx==0)?data4 : (idx==1)?data0 : (idx==2)?data1 :
                         (idx==3)?data2 : (idx==4)?data3 : (idx==5)?data5 : 4'b0;
      3'b101: exp_mux = (idx==0)?data5 : (idx==1)?data0 : (idx==2)?data1 :
                         (idx==3)?data2 : (idx==4)?data3 : (idx==5)?data4 : 4'b0;
      default: exp_mux = 4'b0000;
    endcase
  endfunction

  function automatic logic [2:0] exp_hp ();
    if      (exp_mux(5) > 4'b0000) exp_hp = 3'b101;
    else if (exp_mux(4) > 4'b0000) exp_hp = 3'b100;
    else if (exp_mux(3) > 4'b0000) exp_hp = 3'b011;
    else if (exp_mux(2) > 4'b0000) exp_hp = 3'b010;
    else if (exp_mux(1) > 4'b0000) exp_hp = 3'b001;
    else if (exp_mux(0) > 4'b0000) exp_hp = 3'b000;
    else                           exp_hp = 3'b000;
  endfunction

  function automatic logic [3:0] exp_out ();
    exp_out = exp_mux(exp_hp());
  endfunction

  // Core functional assertions
  // 1) Reordering correctness
  assert property (@comb_ev
    (mux_out[0] == exp_mux(0)) && (mux_out[1] == exp_mux(1)) &&
    (mux_out[2] == exp_mux(2)) && (mux_out[3] == exp_mux(3)) &&
    (mux_out[4] == exp_mux(4)) && (mux_out[5] == exp_mux(5))
  ) else $error("mux_out mapping mismatch");

  // 2) Priority encoder correctness
  assert property (@comb_ev highest_priority == exp_hp())
    else $error("highest_priority mismatch");

  // 3) Decoder mirrors encoder
  assert property (@comb_ev selected_input == highest_priority)
    else $error("selected_input != highest_priority");

  // 4) Output equals selected mux element
  assert property (@comb_ev out == mux_out[selected_input])
    else $error("out != mux_out[selected_input]");

  // 5) End-to-end functional equivalence
  assert property (@comb_ev out == exp_out())
    else $error("End-to-end out mismatch");

  // Targeted corner assertions
  // Invalid sel (110/111) must zero out
  assert property (@comb_ev (sel inside {3'b110,3'b111}) |-> (out == 4'b0000))
    else $error("Invalid sel must yield out=0");

  // All-zero inputs must yield out=0
  assert property (@comb_ev ((data0|data1|data2|data3|data4|data5) == 4'b0000) |-> (out == 4'b0000))
    else $error("All-zero inputs must yield out=0");

  // Coverage
  cover property (@comb_ev sel == 3'b000);
  cover property (@comb_ev sel == 3'b001);
  cover property (@comb_ev sel == 3'b010);
  cover property (@comb_ev sel == 3'b011);
  cover property (@comb_ev sel == 3'b100);
  cover property (@comb_ev sel == 3'b101);
  cover property (@comb_ev sel inside {3'b110,3'b111});

  cover property (@comb_ev exp_hp() == 3'b000);
  cover property (@comb_ev exp_hp() == 3'b001);
  cover property (@comb_ev exp_hp() == 3'b010);
  cover property (@comb_ev exp_hp() == 3'b011);
  cover property (@comb_ev exp_hp() == 3'b100);
  cover property (@comb_ev exp_hp() == 3'b101);
  cover property (@comb_ev exp_out() == 4'b0000); // all-zero case observed

endmodule

// Bind example (bind to the module type so internals are visible by name)
bind mux_priority_encoder_decoder mux_priority_encoder_decoder_sva sva_inst (
  .sel(sel),
  .data0(data0), .data1(data1), .data2(data2),
  .data3(data3), .data4(data4), .data5(data5),
  .out(out),
  .mux_out(mux_out),
  .highest_priority(highest_priority),
  .selected_input(selected_input)
);