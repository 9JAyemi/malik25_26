
module rr_event_picker(
  input rclk,
  input grst_l,
  input arst_l,
  input si,
  input se,
  input [3:0] events,
  input [3:0] events_picked,
  input [3:0] thread_force,
  output [3:0] pick_one_hot
);

  wire         clk;
  wire         reset,dbb_reset_l ;
  wire  [3:0]  thread_force_pe_mask ;
  wire  [3:0]  pick_thread_force_1hot ;
  wire         thread_force_events_sel ;
  wire  [3:0]  pick_rrobin_1hot, pick_rev_rrobin_1hot, pick_rrobin_1hot_mx ;
  wire         events_pick_dir_d1 ;
  wire         events_pick_dir ;
  wire  [3:0]  pick_rrobin_status_or_one_hot ;
  wire  [3:0]  pick_rrobin_din ;
  wire  [3:0]  pick_rrobin ;
  wire         pick_rrobin_reset ;
  wire         pick_rrobin_dir_upd ;
  wire  [3:0]  pick_rrobin_events ;

  reg         dbb_rstff_Q;
  reg  [3:0]  pick_rrobin_inst_Q;
  reg         events_pick_dir_inst_Q;

  assign clk = rclk;

  assign	reset =  ~dbb_reset_l;

  assign	thread_force_events_sel = |(events[3:0] & thread_force[3:0]) ;

  assign  thread_force_pe_mask[3:0]  =  events[3:0] & thread_force[3:0] ;
  assign	pick_thread_force_1hot[0] = thread_force_pe_mask[0] ;
  assign	pick_thread_force_1hot[1] = thread_force_pe_mask[1] & ~thread_force_pe_mask[0] ;
  assign	pick_thread_force_1hot[2] = thread_force_pe_mask[2] & ~|thread_force_pe_mask[1:0] ;
  assign	pick_thread_force_1hot[3] = thread_force_pe_mask[3] & ~|thread_force_pe_mask[2:0] ;

  assign  pick_rrobin_events[3:0]  =  events[3:0] & ~pick_rrobin[3:0] ;

  assign  pick_rrobin_1hot[0] = ~events_pick_dir_d1 & pick_rrobin_events[0] ;
  assign	pick_rrobin_1hot[1] = ~events_pick_dir_d1 & pick_rrobin_events[1] & ~pick_rrobin_events[0] ;
  assign	pick_rrobin_1hot[2] = ~events_pick_dir_d1 & pick_rrobin_events[2] & ~|pick_rrobin_events[1:0] ;
  assign	pick_rrobin_1hot[3] = ~events_pick_dir_d1 & pick_rrobin_events[3] & ~|pick_rrobin_events[2:0] ;

  assign  pick_rev_rrobin_1hot[0] = events_pick_dir_d1 & pick_rrobin_events[0] & ~|pick_rrobin_events[3:1] ;
  assign	pick_rev_rrobin_1hot[1] = events_pick_dir_d1 & pick_rrobin_events[1] & ~|pick_rrobin_events[3:2] ;
  assign	pick_rev_rrobin_1hot[2] = events_pick_dir_d1 & pick_rrobin_events[2] & ~|pick_rrobin_events[3] ;
  assign	pick_rev_rrobin_1hot[3] = events_pick_dir_d1 & pick_rrobin_events[3] ;

  assign  pick_rrobin_1hot_mx[3:0]  =  pick_rev_rrobin_1hot[3:0] | pick_rrobin_1hot[3:0] ;
  assign  pick_one_hot[3:0]    =  thread_force_events_sel ? pick_thread_force_1hot[3:0] : 
                                                          pick_rrobin_1hot_mx[3:0] ;

  assign pick_rrobin_status_or_one_hot[3:0] = pick_rrobin[3:0] | events_picked[3:0] ;
  assign pick_rrobin_reset = reset | ~|(events[3:0] & ~pick_rrobin_status_or_one_hot[3:0]) ;
  assign pick_rrobin_dir_upd = |events[3:0] & (~|(events[3:0] & ~pick_rrobin_status_or_one_hot[3:0])) ;

  assign events_pick_dir  =  ~reset &
                           (( ~pick_rrobin_dir_upd & events_pick_dir_d1) |		//hold
                            (  pick_rrobin_dir_upd & ~events_pick_dir_d1)) ;		//set - invert direction
   
  always @(posedge clk) begin
    dbb_rstff_Q <= (~arst_l | grst_l) & (dbb_rstff_Q & ~se);
  end
  assign dbb_reset_l = dbb_rstff_Q;

  always @(posedge clk) begin
    if (~reset) begin
      pick_rrobin_inst_Q <= 4'b0;
    end else begin
      pick_rrobin_inst_Q <= pick_rrobin_din;
    end
  end
  assign pick_rrobin = pick_rrobin_inst_Q;

  always @(posedge clk) begin
    if (reset) begin
      events_pick_dir_inst_Q <= 1'b0;
    end else begin
      events_pick_dir_inst_Q <= events_pick_dir;
    end
  end
  assign events_pick_dir_d1 = events_pick_dir_inst_Q;

  assign pick_rrobin_din[3:0] = pick_rrobin_reset ? 4'b0 :
                              (pick_rrobin_dir_upd ? {pick_rrobin_events[2:0], pick_rrobin_events[3]} :
                              pick_rrobin_events) ;
endmodule
