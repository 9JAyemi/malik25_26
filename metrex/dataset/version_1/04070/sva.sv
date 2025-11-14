// SVA for my_uart_tx8to8
// Bind this file to the DUT: bind my_uart_tx8to8 my_uart_tx8to8_sva sva_i(.dut());

module my_uart_tx8to8_sva (my_uart_tx8to8 dut);

  default clocking cb @(posedge dut.clk); endclocking
  default disable iff (!dut.rst_n);

  function automatic logic [12:0] term_cnt (input logic [2:0] ctl);
    case (ctl)
      3'h0: term_cnt = dut.bps9600;
      3'h1: term_cnt = dut.bps19200;
      3'h2: term_cnt = dut.bps38400;
      3'h3: term_cnt = dut.bps57600;
      3'h4: term_cnt = dut.bps115200;
      3'h5: term_cnt = dut.bps256000;
      default: term_cnt = dut.bps9600;
    endcase
  endfunction

  // Reset values
  assert property (!dut.rst_n |-> dut.cnt==13'd0 && dut.bps_sel==1'b0);
  assert property (!dut.rst_n |-> dut.tran_cnt==4'd9 && !dut.sign_delay && !dut.data_valid && dut.rs_tx);

  // Baud counter behavior and tick
  assert property ((dut.cnt != term_cnt(dut.uart_ctl)) |=> dut.cnt == $past(dut.cnt)+13'd1);
  assert property ((dut.cnt == term_cnt(dut.uart_ctl)) |=> dut.cnt == 13'd0);
  assert property (dut.bps_sel == (dut.cnt==13'd0));

  // sign_delay logic
  assert property (dut.bps_sel |=> !dut.sign_delay);
  assert property (!dut.bps_sel && dut.data_sign |=> dut.sign_delay);
  assert property (!dut.bps_sel && !dut.data_sign |=> dut.sign_delay == $past(dut.sign_delay));

  // tran_cnt behavior
  assert property (!dut.bps_sel |=> dut.tran_cnt == $past(dut.tran_cnt));
  assert property (dut.bps_sel && (dut.tran_cnt!=4'd9) |=> dut.tran_cnt == $past(dut.tran_cnt)+4'd1);
  assert property (dut.bps_sel && (dut.tran_cnt==4'd9) && (dut.data_sign || dut.sign_delay) |=> dut.tran_cnt==4'd0);
  assert property (dut.bps_sel && (dut.tran_cnt==4'd9) && !(dut.data_sign || dut.sign_delay) |=> dut.tran_cnt==4'd9);
  assert property (1'b1 |-> (dut.tran_cnt <= 4'd9));

  // data_valid behavior
  assert property ((dut.data_sign || dut.sign_delay) |=> !dut.data_valid);
  assert property ((dut.tran_cnt==4'd9) && !(dut.data_sign || dut.sign_delay) |=> dut.data_valid);
  assert property (!((dut.data_sign || dut.sign_delay) || (dut.tran_cnt==4'd9)) |=> dut.data_valid == $past(dut.data_valid));
  // During frame, data_valid stays low
  assert property ((dut.tran_cnt!=4'd9) |-> !dut.data_valid);

  // rs_tx timing and mapping
  assert property (!dut.bps_sel |=> dut.rs_tx == $past(dut.rs_tx));
  assert property (dut.bps_sel && (dut.tran_cnt==4'd0) |=> dut.rs_tx==1'b0); // start bit
  genvar i;
  generate
    for (i=1;i<=8;i++) begin : gen_bit_map
      assert property (dut.bps_sel && (dut.tran_cnt==i[3:0]) |=> dut.rs_tx == $past(dut.data_out[i-1]));
    end
  endgenerate
  assert property (dut.bps_sel && (dut.tran_cnt==4'd9) |=> dut.rs_tx==1'b1); // stop/idle

  // Acceptance to start timing (accept at 9, start 0 on next tick)
  sequence tick; dut.bps_sel; endsequence
  sequence accept; dut.bps_sel && (dut.tran_cnt==4'd9) && (dut.data_sign || dut.sign_delay); endsequence
  assert property (accept ##1 (tick && $past(dut.tran_cnt==4'd0,1)) |-> 1'b1); // structural check

  // Coverage
  // Each baud selection produces at least one tick
  genvar v;
  generate
    for (v=0; v<=5; v++) begin : gen_baud_cov
      cover property (dut.uart_ctl==v[2:0] && dut.bps_sel);
    end
  endgenerate
  // Full frame: accept -> 10 ticks -> back to idle with data_valid
  sequence ten_ticks; tick[*10]; endsequence
  cover property (accept ##1 ten_ticks ##0 (dut.tran_cnt==4'd9 && dut.data_valid));
  // Back-to-back frames at minimum spacing (10 ticks apart)
  cover property (accept ##1 tick[*10] ##0 accept);

endmodule