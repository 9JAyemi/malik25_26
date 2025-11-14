// SVA for is2vid_control
// Bind-ready, focuses on key protocol, register map, and sticky/handshake behavior.
// Quality over quantity; concise but covers essentials.

module is2vid_control_sva
  #(parameter USE_CONTROL = 1,
    parameter NO_OF_MODES_INT = 1,
    parameter USED_WORDS_WIDTH = 15)
(
  input  wire rst,
  input  wire clk,

  // From mode registers
  input  wire av_write_ack,
  input  wire mode_change,
  input  wire [NO_OF_MODES_INT-1:0] mode_match,

  // From FIFO
  input  wire [USED_WORDS_WIDTH-1:0] usedw,
  input  wire underflow_sticky,
  input  wire enable_resync,
  input  wire genlocked,

  // IS2Vid control signals
  input  wire enable,
  input  wire clear_underflow_sticky,
  input  wire write_trigger,
  input  wire write_trigger_ack,
  input  wire [1:0] genlock_enable,

  // Avalon-MM slave port
  input  wire [7:0] av_address,
  input  wire       av_read,
  input  wire [15:0] av_readdata,
  input  wire       av_write,
  input  wire [15:0] av_writedata,
  input  wire       av_waitrequest,

  input  wire status_update_int
);

  default clocking cb @(posedge clk); endclocking

  function automatic bit is_side_addr(input [7:0] a);
    return (a <= 8'd4);
  endfunction

  // Mirrors for control fields to enable strong assertions without hierarchical access
  logic [1:0] mir_int_en;
  logic [1:0] mir_genlock_en;
  logic       mir_enable;
  logic [NO_OF_MODES_INT-1:0] mir_mode_match;

  always_ff @(posedge clk or posedge rst) begin
    if (rst) begin
      mir_int_en      <= '0;
      mir_genlock_en  <= '0;
      mir_enable      <= 1'b0;
      mir_mode_match  <= '0;
    end else begin
      if (av_write && (av_address == 8'd0)) begin
        {mir_genlock_en, mir_int_en, mir_enable} <= av_writedata[4:0];
      end
      if (mode_change) begin
        mir_mode_match <= mode_match;
      end
    end
  end

  // Helper functions for expected read data
  function automatic [15:0] exp_usedw_16(input [USED_WORDS_WIDTH-1:0] uw);
    if (USED_WORDS_WIDTH >= 16) exp_usedw_16 = uw[15:0];
    else                        exp_usedw_16 = {{16-USED_WORDS_WIDTH{1'b0}}, uw};
  endfunction

  function automatic [15:0] exp_mode_match_16(input [NO_OF_MODES_INT-1:0] mm);
    if (NO_OF_MODES_INT >= 16) exp_mode_match_16 = mm[15:0];
    else                       exp_mode_match_16 = {{16-NO_OF_MODES_INT{1'b0}}, mm};
  endfunction

generate
if (USE_CONTROL) begin : g_use_ctrl
  // Reset values visible at outputs
  assert property (@(posedge clk) rst |-> (enable==1'b0 && status_update_int==1'b0
                                           && clear_underflow_sticky==1'b0
                                           && write_trigger_ack==1'b0
                                           && genlock_enable==2'b00));

  // write_trigger combinational decode
  assert property (disable iff (rst) (write_trigger == (av_write && !is_side_addr(av_address))));

  // Non-side write waitrequest protocol
  assert property (disable iff (rst) (av_write && !is_side_addr(av_address) && !av_write_ack) |-> av_waitrequest);
  assert property (disable iff (rst) (av_write && !is_side_addr(av_address) &&  av_write_ack) |-> !av_waitrequest);
  // Side-register writes never wait
  assert property (disable iff (rst) (av_write &&  is_side_addr(av_address)) |-> !av_waitrequest);

  // write_trigger_ack is 1-cycle delayed av_write_ack
  assert property (@(posedge clk) rst |-> (write_trigger_ack==1'b0));
  assert property (@(posedge clk) disable iff (rst) $past(!rst) |-> (write_trigger_ack == $past(av_write_ack)));

  // Control register write -> outputs update next cycle
  assert property (disable iff (rst)
                   (av_write && (av_address==8'd0)) |=> (enable==av_writedata[0] && genlock_enable==av_writedata[4:3]));

  // Mirror consistency: outputs follow mirrors
  assert property (disable iff (rst) (enable == mir_enable));
  assert property (disable iff (rst) (genlock_enable == mir_genlock_en));

  // Read map assertions
  // addr 1: {12'b0, genlocked, underflow_sticky, 1'b0, enable_resync}
  assert property (disable iff (rst)
                   (av_address==8'd1 && av_read) |-> (av_readdata[15:4]==12'b0
                                                      && av_readdata[3]==genlocked
                                                      && av_readdata[2]==underflow_sticky
                                                      && av_readdata[1]==1'b0
                                                      && av_readdata[0]==enable_resync));
  // addr 2: {13'b0, genlocked_int_reg, status_update_int_reg, 1'b0}
  // Bit0 must be 0; upper zeros
  assert property (disable iff (rst)
                   (av_address==8'd2 && av_read) |-> (av_readdata[15:3]==13'b0 && av_readdata[0]==1'b0));
  // status_update_int equals OR of bits exposed at addr 2 when read
  assert property (disable iff (rst)
                   (av_address==8'd2 && av_read) |-> (status_update_int == (av_readdata[2] | av_readdata[1])));

  // addr 3: usedw mapping
  assert property (disable iff (rst)
                   (av_address==8'd3 && av_read) |-> (av_readdata == exp_usedw_16(usedw)));

  // addr 4: mode_match mapping (mirror of last latched on mode_change)
  assert property (disable iff (rst)
                   (av_address==8'd4 && av_read) |-> (av_readdata == exp_mode_match_16(mir_mode_match)));

  // default: {11'b0, genlock_enable, interrupt_enable, enable}
  assert property (disable iff (rst)
                   (av_read && (av_address!=8'd1) && (av_address!=8'd2) && (av_address!=8'd3) && (av_address!=8'd4))
                   |-> (av_readdata[15:5]==11'b0
                        && av_readdata[4:3]==genlock_enable
                        && av_readdata[2:1]==mir_int_en
                        && av_readdata[0]==enable));

  // Control write/readback coherency
  assert property (disable iff (rst)
                   (av_write && av_address==8'd0 ##1 av_read && av_address==8'd0)
                   |-> (av_readdata[4:3]==$past(av_writedata[4:3]) &&
                        av_readdata[2:1]==$past(av_writedata[2:1]) &&
                        av_readdata[0]  ==$past(av_writedata[0])));

  // Status interrupt behavior (using mirrored enables)
  // mode_change -> status_update_int sets when enabled
  assert property (disable iff (rst) (mode_change && mir_int_en[0]) |=> status_update_int);

  // genlocked change -> status_update_int sets when enabled
  assert property (disable iff (rst) ($changed(genlocked) && mir_int_en[1]) |=> status_update_int);

  // If both sources disabled, status_update_int must be 0
  assert property (disable iff (rst) (mir_int_en==2'b00) |-> !status_update_int);

  // Clear individual sources: when the other source disabled, status line must deassert
  assert property (disable iff (rst)
                   (av_write && av_address==8'd2 && av_writedata[1] && (mir_int_en[1]==1'b0)) |=> !status_update_int);
  assert property (disable iff (rst)
                   (av_write && av_address==8'd2 && av_writedata[2] && (mir_int_en[0]==1'b0)) |=> !status_update_int);

  // clear_underflow_sticky gating: only high when underflow_sticky is high
  assert property (disable iff (rst) clear_underflow_sticky |-> underflow_sticky);
  // Request to clear underflow -> sticky clear asserted next cycle and held while underflow_sticky remains high
  assert property (disable iff (rst)
                   (av_write && av_address==8'd1 && av_writedata[2] && underflow_sticky)
                   |=> clear_underflow_sticky until_with (!underflow_sticky));
  // When underflow_sticky drops, clear_underflow_sticky must drop next cycle
  assert property (disable iff (rst) (!underflow_sticky) |=> (!clear_underflow_sticky));

  // Covers
  cover property (disable iff (rst) (av_write && av_address==8'd0 ##1 av_read && av_address==8'd0));
  cover property (disable iff (rst) (av_write && !is_side_addr(av_address) && !av_write_ack ##1 av_write && !is_side_addr(av_address) && av_write_ack));
  cover property (disable iff (rst) (mode_change && mir_int_en[0] ##1 status_update_int ##1 av_write && av_address==8'd2 && av_writedata[1] ##1 !status_update_int));
  cover property (disable iff (rst) ($changed(genlocked) && mir_int_en[1] ##1 status_update_int ##1 av_write && av_address==8'd2 && av_writedata[2] ##1 !status_update_int));
  cover property (disable iff (rst) (av_read && av_address==8'd3));
  cover property (disable iff (rst) (mode_change ##1 av_read && av_address==8'd4));
  cover property (disable iff (rst) (av_write && av_address==8'd1 && av_writedata[2] && underflow_sticky ##1 clear_underflow_sticky));

end else begin : g_no_ctrl
  // Constant outputs when USE_CONTROL==0
  assert property (@(posedge clk) 1 |-> (enable==1'b1 && status_update_int==1'b0 &&
                                         clear_underflow_sticky==1'b0 &&
                                         write_trigger==1'b0 && write_trigger_ack==1'b0 &&
                                         genlock_enable==2'b00 && av_waitrequest==1'b0 &&
                                         av_readdata==16'b0));
  // Cover a few bus activities to confirm stability under traffic
  cover property (disable iff (rst) (av_write ##1 av_read));
end
endgenerate

endmodule

// Bind into the DUT
bind is2vid_control is2vid_control_sva #(.USE_CONTROL(USE_CONTROL),
                                         .NO_OF_MODES_INT(NO_OF_MODES_INT),
                                         .USED_WORDS_WIDTH(USED_WORDS_WIDTH)) u_is2vid_control_sva (.*);