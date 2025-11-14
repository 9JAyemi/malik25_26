// SVA for rxuart
// Bind this file to the DUT:
//   bind rxuart rxuart_sva u_rxuart_sva (.*);

module rxuart_sva (
  input  wire        i_clk, i_reset,
  input  wire [30:0] i_setup,
  input  wire        i_uart_rx,
  input  wire        o_wr,
  input  wire [7:0]  o_data,
  input  wire        o_break,
  input  wire        o_parity_err, o_frame_err,
  input  wire        o_ck_uart,

  input  wire [29:0] r_setup,
  input  wire [3:0]  state,

  input  wire [27:0] baud_counter,
  input  wire        zero_baud_counter,

  input  wire        q_uart, qq_uart, ck_uart,
  input  wire [27:0] chg_counter,
  input  wire        line_synch,
  input  wire        half_baud_time,
  input  wire [7:0]  data_reg,
  input  wire        calc_parity,
  input  wire        pre_wr
);

  // Local decode (mirror DUT encodings)
  localparam [3:0] RXU_BIT_ZERO    = 4'h0,
                   RXU_BIT_ONE     = 4'h1,
                   RXU_BIT_TWO     = 4'h2,
                   RXU_BIT_THREE   = 4'h3,
                   RXU_BIT_SEVEN   = 4'h7,
                   RXU_PARITY      = 4'h8,
                   RXU_STOP        = 4'h9,
                   RXU_SECOND_STOP = 4'ha,
                   RXU_BREAK       = 4'hd,
                   RXU_RESET_IDLE  = 4'he,
                   RXU_IDLE        = 4'hf;

  // Derived fields (same as DUT)
  wire [27:0] clocks_per_baud = {4'h0, r_setup[23:0]};
  wire [1:0]  data_bits       = r_setup[29:28];
  wire        dblstop         = r_setup[27];
  wire        use_parity      = r_setup[26];
  wire        fixd_parity     = r_setup[25];
  wire        parity_even     = r_setup[24];
  wire [27:0] break_condition = {r_setup[23:0], 4'h0};
  wire [27:0] half_baud       = {5'h00, r_setup[23:1]} - 28'h1;

  default clocking cb @(posedge i_clk); endclocking
  default disable iff (i_reset);

  // Synchronizer pipeline and export
  assert property (qq_uart == $past(q_uart));
  assert property (ck_uart == $past(qq_uart));
  assert property (o_ck_uart == ck_uart);

  // Change counter behavior and derived flags
  assert property ((qq_uart != ck_uart) |-> chg_counter == 28'h0);
  assert property ((qq_uart == ck_uart && chg_counter < break_condition) |-> chg_counter == $past(chg_counter)+1);
  assert property ((chg_counter >= break_condition) |-> chg_counter >= break_condition);
  assert property (o_break == ((chg_counter >= break_condition) && (~ck_uart)));
  assert property (line_synch == ((chg_counter >= break_condition) && (ck_uart)));
  assert property (half_baud_time == ((~ck_uart) && (chg_counter >= half_baud)));

  // Setup register update policy
  assert property ((state >= RXU_RESET_IDLE) |-> r_setup == $past(i_setup[29:0]));
  assert property ((state <  RXU_RESET_IDLE) |-> r_setup == $past(r_setup));

  // zero_baud_counter and baud_counter rules
  assert property (state == RXU_IDLE |-> !zero_baud_counter);
  assert property (state != RXU_IDLE |-> zero_baud_counter == (baud_counter == 28'h01));

  assert property (zero_baud_counter |=> baud_counter == clocks_per_baud-28'h01);
  assert property ((state inside {RXU_RESET_IDLE,RXU_BREAK,RXU_IDLE}) && !zero_baud_counter |-> baud_counter == clocks_per_baud-28'h01);
  assert property (!(state inside {RXU_RESET_IDLE,RXU_BREAK,RXU_IDLE}) && !zero_baud_counter |-> baud_counter == $past(baud_counter)-28'h01);

  // State transitions
  assert property (state == RXU_RESET_IDLE && !line_synch |=> state == RXU_RESET_IDLE);
  assert property (state == RXU_RESET_IDLE && line_synch  |=> state == RXU_IDLE);

  assert property (o_break |=> state == RXU_BREAK);
  assert property (state == RXU_BREAK &&  ck_uart |=> state == RXU_IDLE);
  assert property (state == RXU_BREAK && !ck_uart |=> state == RXU_BREAK);

  assert property (state == RXU_IDLE && (~ck_uart && half_baud_time) |=> (
                     (data_bits==2'b00 && state==RXU_BIT_ZERO)  ||
                     (data_bits==2'b01 && state==RXU_BIT_ONE)   ||
                     (data_bits==2'b10 && state==RXU_BIT_TWO)   ||
                     (data_bits==2'b11 && state==RXU_BIT_THREE)));
  assert property (state == RXU_IDLE && !(~ck_uart && half_baud_time) |=> state == RXU_IDLE);

  // Bit/Parity/Stop progression on baud strobe
  assert property (zero_baud_counter && (state < RXU_BIT_SEVEN) |=> state == $past(state)+1);
  assert property (zero_baud_counter && (state == RXU_BIT_SEVEN) |=> state == (use_parity ? RXU_PARITY : RXU_STOP));
  assert property (zero_baud_counter && (state == RXU_PARITY)    |=> state == RXU_STOP);
  assert property (zero_baud_counter && (state == RXU_STOP) &&  ~ck_uart |=> state == RXU_RESET_IDLE);
  assert property (zero_baud_counter && (state == RXU_STOP) &&   ck_uart &&  dblstop |=> state == RXU_SECOND_STOP);
  assert property (zero_baud_counter && (state == RXU_STOP) &&   ck_uart && !dblstop |=> state == RXU_IDLE);
  assert property (zero_baud_counter && (state == RXU_SECOND_STOP) && ~ck_uart |=> state == RXU_RESET_IDLE);
  assert property (zero_baud_counter && (state == RXU_SECOND_STOP) &&  ck_uart |=> state == RXU_IDLE);

  // Shift register behavior
  assert property (zero_baud_counter && (state != RXU_PARITY) |=> data_reg == {ck_uart, $past(data_reg)[7:1]});

  // Parity accumulator behavior
  assert property (state == RXU_IDLE |=> calc_parity == 1'b0);
  assert property (state != RXU_IDLE && !zero_baud_counter |-> calc_parity == $past(calc_parity));
  assert property (state != RXU_IDLE &&  zero_baud_counter |=> calc_parity == ($past(calc_parity) ^ ck_uart));

  // Parity error reporting
  assert property (zero_baud_counter && state == RXU_PARITY && fixd_parity |=> o_parity_err == (ck_uart ^ parity_even));
  assert property (zero_baud_counter && state == RXU_PARITY && !fixd_parity && parity_even |=> o_parity_err == (calc_parity != ck_uart));
  assert property (zero_baud_counter && state == RXU_PARITY && !fixd_parity && !parity_even |=> o_parity_err == (calc_parity == ck_uart));
  assert property ((state >= RXU_BREAK) |=> o_parity_err == 1'b0);

  // Framing error reporting
  assert property (zero_baud_counter && (state==RXU_STOP || state==RXU_SECOND_STOP)
                   |=> o_frame_err == ($past(o_frame_err) || ~ck_uart));
  assert property ((zero_baud_counter || state >= RXU_BREAK) && !(state==RXU_STOP || state==RXU_SECOND_STOP)
                   |=> o_frame_err == 1'b0);

  // Data latch and write strobe
  assert property (zero_baud_counter && state == RXU_STOP |=> pre_wr);
  assert property ((zero_baud_counter || state == RXU_IDLE) |=> !pre_wr);

  assert property (zero_baud_counter && state == RXU_STOP && data_bits==2'b00 |=> o_data == data_reg);
  assert property (zero_baud_counter && state == RXU_STOP && data_bits==2'b01 |=> o_data == {1'b0, $past(data_reg)[7:1]});
  assert property (zero_baud_counter && state == RXU_STOP && data_bits==2'b10 |=> o_data == {2'b0, $past(data_reg)[7:2]});
  assert property (zero_baud_counter && state == RXU_STOP && data_bits==2'b11 |=> o_data == {3'b0, $past(data_reg)[7:3]});

  assert property ((zero_baud_counter || state == RXU_IDLE) |=> o_wr == (pre_wr && !i_reset));
  assert property (!(zero_baud_counter || state == RXU_IDLE) |=> o_wr == 1'b0);

  // Basic safety: no baud strobe in IDLE
  assert property (state == RXU_IDLE |-> !zero_baud_counter);

  // Coverage
  cover property (
    state == RXU_IDLE && (~ck_uart && half_baud_time)
    ##1 (data_bits==2'b00 ? state==RXU_BIT_ZERO :
         data_bits==2'b01 ? state==RXU_BIT_ONE  :
         data_bits==2'b10 ? state==RXU_BIT_TWO  :
                            state==RXU_BIT_THREE)
    ##[1:$] zero_baud_counter [*8]
    ##1 state==RXU_STOP && ck_uart && !dblstop ##1 o_wr && !o_parity_err && !o_frame_err);

  cover property (
    use_parity && parity_even && !fixd_parity
    ##1 state==RXU_PARITY ##1 zero_baud_counter && !o_parity_err);

  cover property (
    use_parity && !parity_even && !fixd_parity
    ##1 state==RXU_PARITY ##1 zero_baud_counter && o_parity_err);

  cover property (
    state==RXU_STOP ##1 zero_baud_counter && ~ck_uart ##1 state==RXU_RESET_IDLE);

  cover property (
    dblstop && state==RXU_STOP && ck_uart ##1 zero_baud_counter ##1 state==RXU_SECOND_STOP && ck_uart ##1 o_wr);

  cover property (
    (~ck_uart) throughout (chg_counter >= break_condition) ##1 o_break ##1 state==RXU_BREAK ##[1:$] ck_uart ##1 state==RXU_IDLE);

endmodule