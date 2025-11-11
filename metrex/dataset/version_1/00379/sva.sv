// SVA for uniphy_status. Bind this file to the DUT.
// Focused, concise checks with full functional coverage.

module uniphy_status_sva
  #(parameter int WIDTH = 32,
    parameter int NUM_UNIPHYS = 2)
(
   input  logic                   clk,
   input  logic                   resetn,

   input  logic                   slave_read,
   input  logic [WIDTH-1:0]       slave_readdata,

   input  logic  mem0_local_cal_success,
   input  logic  mem0_local_cal_fail,
   input  logic  mem0_local_init_done,

   input  logic  mem1_local_cal_success,
   input  logic  mem1_local_cal_fail,
   input  logic  mem1_local_init_done,

   input  logic  mem2_local_cal_success,
   input  logic  mem2_local_cal_fail,
   input  logic  mem2_local_init_done,

   input  logic  mem3_local_cal_success,
   input  logic  mem3_local_cal_fail,
   input  logic  mem3_local_init_done,

   input  logic  mem4_local_cal_success,
   input  logic  mem4_local_cal_fail,
   input  logic  mem4_local_init_done,

   input  logic  mem5_local_cal_success,
   input  logic  mem5_local_cal_fail,
   input  logic  mem5_local_init_done,

   input  logic  mem6_local_cal_success,
   input  logic  mem6_local_cal_fail,
   input  logic  mem6_local_init_done,

   input  logic  mem7_local_cal_success,
   input  logic  mem7_local_cal_fail,
   input  logic  mem7_local_init_done,

   input  logic  export_local_cal_success,
   input  logic  export_local_cal_fail,
   input  logic  export_local_init_done
);

  // Clamp used PHYs to [0..8]
  localparam int USED = (NUM_UNIPHYS < 1) ? 0 : ((NUM_UNIPHYS > 8) ? 8 : NUM_UNIPHYS);

  // Build 8-bit vectors [7:0] = {mem7..mem0}
  logic [7:0] v_succ, v_fail, v_init;
  assign v_succ = { mem7_local_cal_success, mem6_local_cal_success, mem5_local_cal_success, mem4_local_cal_success,
                    mem3_local_cal_success, mem2_local_cal_success, mem1_local_cal_success, mem0_local_cal_success };
  assign v_fail = { mem7_local_cal_fail,    mem6_local_cal_fail,    mem5_local_cal_fail,    mem4_local_cal_fail,
                    mem3_local_cal_fail,    mem2_local_cal_fail,    mem1_local_cal_fail,    mem0_local_cal_fail    };
  assign v_init = { mem7_local_init_done,   mem6_local_init_done,   mem5_local_init_done,   mem4_local_init_done,
                    mem3_local_init_done,   mem2_local_init_done,   mem1_local_init_done,   mem0_local_init_done   };

  // Expected mask and aggregated booleans (match DUT equations)
  logic [7:0] mask_exp;
  assign mask_exp = (NUM_UNIPHYS < 1) ? 8'h00 :
                    (NUM_UNIPHYS >= 8) ? 8'hff :
                    ~(8'hff << NUM_UNIPHYS);

  logic exp_cal_success, exp_cal_fail, exp_init_done;
  assign exp_cal_success = &(~mask_exp | v_succ);
  assign exp_cal_fail    = |v_fail;
  assign exp_init_done   = &(~mask_exp | v_init);

  // Expected slave_readdata image
  logic [WIDTH-1:0] exp_agg;
  always_comb begin
    exp_agg = '0;
    if (WIDTH > 0) exp_agg[0] = ~exp_init_done;
    if (WIDTH > 1) exp_agg[1] = exp_cal_fail;
    if (WIDTH > 2) exp_agg[2] = ~exp_cal_success;
    if (WIDTH > 3) exp_agg[3] = 1'b0;
    for (int i = 0; i < USED; i++) begin
      if ((4+i) < WIDTH) exp_agg[4+i] = ~v_init[i]; // not_init_done[i]
    end
    // All bits beyond 4+USED-1 are already 0 by initialization
  end

  // Reset: read data clears to 0
  assert property (@(posedge clk) !resetn |-> (slave_readdata == '0))
    else $error("uniphy_status: slave_readdata not cleared on reset");

  // Registered image equals expected pack of status bits every cycle out of reset
  assert property (@(posedge clk) disable iff (!resetn) slave_readdata == exp_agg)
    else $error("uniphy_status: slave_readdata mapping mismatch");

  // Exported comb outputs match expected reductions
  assert property (@(posedge clk) disable iff (!resetn)
                   (export_local_cal_success == exp_cal_success) &&
                   (export_local_cal_fail    == exp_cal_fail)    &&
                   (export_local_init_done   == exp_init_done))
    else $error("uniphy_status: export_* outputs mismatch expected");

  // Per-PHY sanity: success/fail mutually exclusive for used PHYs
  generate
    for (genvar i = 0; i < USED; i++) begin : g_mut_excl
      logic s, f;
      assign s = v_succ[i];
      assign f = v_fail[i];
      assert property (@(posedge clk) disable iff (!resetn) !(s && f))
        else $error("uniphy_status: PHY %0d cal_success and cal_fail both high", i);
    end
  endgenerate

  // Functional cover: key scenarios seen at least once
  cover property (@(posedge clk) resetn && exp_init_done && exp_cal_success && !exp_cal_fail);
  cover property (@(posedge clk) resetn && exp_cal_fail);
  cover property (@(posedge clk) resetn && (|(mask_exp & ~v_init)));

endmodule

// Bind to DUT
bind uniphy_status uniphy_status_sva #(.WIDTH(WIDTH), .NUM_UNIPHYS(NUM_UNIPHYS)) uniphy_status_sva_i
(
  .clk,
  .resetn,
  .slave_read,
  .slave_readdata,
  .mem0_local_cal_success,
  .mem0_local_cal_fail,
  .mem0_local_init_done,
  .mem1_local_cal_success,
  .mem1_local_cal_fail,
  .mem1_local_init_done,
  .mem2_local_cal_success,
  .mem2_local_cal_fail,
  .mem2_local_init_done,
  .mem3_local_cal_success,
  .mem3_local_cal_fail,
  .mem3_local_init_done,
  .mem4_local_cal_success,
  .mem4_local_cal_fail,
  .mem4_local_init_done,
  .mem5_local_cal_success,
  .mem5_local_cal_fail,
  .mem5_local_init_done,
  .mem6_local_cal_success,
  .mem6_local_cal_fail,
  .mem6_local_init_done,
  .mem7_local_cal_success,
  .mem7_local_cal_fail,
  .mem7_local_init_done,
  .export_local_cal_success,
  .export_local_cal_fail,
  .export_local_init_done
);