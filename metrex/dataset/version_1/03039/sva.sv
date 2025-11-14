// SVA for uart_tx
module uart_tx_sva #(parameter bit ML505 = 1'b0) (
  input  logic        clk,
  input  logic        reset,
  input  logic [1:0]  baud_rate,
  input  logic        ld_tx_data,
  input  logic [7:0]  tx_data,
  input  logic        tx_enable,
  input  logic        tx_out,
  input  logic        tx_empty,
  input  logic [9:0]  baud_cnt,
  input  logic        baud_clk,
  input  logic [7:0]  tx_reg,
  input  logic [3:0]  tx_cnt
);

function automatic int unsigned thr(input bit ml505, input logic [1:0] br);
  if (ml505) return 868;
  else case (br)
    2'd0: return 347;
    2'd1: return 174;
    2'd2: return 87;
    default: return 347;
  endcase
endfunction

default clocking @(posedge clk); endclocking

// Reset behavior
assert property (reset |-> (baud_clk==0 && baud_cnt==0 && tx_reg==8'h00 && tx_empty==1 && tx_out==1 && tx_cnt==0));

// Baud generator: one-cycle pulse, only at threshold; counter progression
assert property (disable iff (reset)
  baud_clk |-> ($past(baud_cnt)==thr(ML505, baud_rate) && baud_cnt==0 ##1 !baud_clk));
assert property (disable iff (reset)
  ($past(baud_cnt)==thr(ML505, baud_rate)) |-> baud_cnt==0);
assert property (disable iff (reset)
  ($past(baud_cnt)!=thr(ML505, baud_rate)) |-> (baud_cnt==$past(baud_cnt)+1 && !baud_clk));
assert property (disable iff (reset) !(baud_clk && $past(baud_clk))); // no multi-cycle high

// TX path changes only on enabled baud tick
assert property (disable iff (reset)
  (!tx_enable || !baud_clk) |=> ($stable(tx_reg) && $stable(tx_cnt) && $stable(tx_out) && $stable(tx_empty)));

// Load -> start bit, go busy (same cycle)
assert property (disable iff (reset)
  (tx_enable && baud_clk && ld_tx_data && tx_empty)
  |-> (tx_reg==tx_data && tx_out==0 && tx_empty==0 && tx_cnt==$past(tx_cnt)));

// Ignore load while busy
assert property (disable iff (reset)
  (tx_enable && baud_clk && ld_tx_data && !tx_empty) |-> ($stable(tx_reg) && tx_empty==0));

// Data bit cycles (cnt 0..7): output matches bit, cnt increments, remains busy
assert property (disable iff (reset)
  (tx_enable && baud_clk && !tx_empty && $past(tx_cnt)<=7)
  |-> (tx_out == ((($past(tx_reg)) >> $past(tx_cnt)) & 1'b1)
       && tx_cnt==$past(tx_cnt)+1 && tx_empty==0));

// Stop bit cycle (cnt==8): line high, empty, cnt reset
assert property (disable iff (reset)
  (tx_enable && baud_clk && !tx_empty && $past(tx_cnt)==8)
  |-> (tx_out==1 && tx_empty==1 && tx_cnt==0));

// Idle line is high when empty
assert property (disable iff (reset) tx_empty |-> tx_out==1);

// tx_empty rises only on a stop event
assert property (disable iff (reset)
  $rose(tx_empty) |-> $past(tx_enable && baud_clk && !$past(tx_empty) && $past(tx_cnt)==8));

// Coverage
cover property (disable iff (reset) (tx_enable && baud_clk && ld_tx_data && tx_empty)); // start event

sequence data_step; (tx_enable && baud_clk && !tx_empty && $past(tx_cnt)<=7); endsequence
cover property (disable iff (reset)
  (tx_enable && baud_clk && ld_tx_data && tx_empty) ##1 data_step[*8] ##1 (tx_enable && baud_clk && $past(tx_cnt)==8)); // full frame

cover property (disable iff (reset) (baud_rate==2'd0) ##1 baud_clk);
cover property (disable iff (reset) (baud_rate==2'd1) ##1 baud_clk);
cover property (disable iff (reset) (baud_rate==2'd2) ##1 baud_clk);

endmodule

// Bind into DUT
bind uart_tx uart_tx_sva #(.ML505(ML505)) uart_tx_sva_i (
  .clk(clk), .reset(reset), .baud_rate(baud_rate), .ld_tx_data(ld_tx_data),
  .tx_data(tx_data), .tx_enable(tx_enable), .tx_out(tx_out), .tx_empty(tx_empty),
  .baud_cnt(baud_cnt), .baud_clk(baud_clk), .tx_reg(tx_reg), .tx_cnt(tx_cnt)
);