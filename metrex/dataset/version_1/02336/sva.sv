// SVA for my_uart_rx8to8
// Bind-in module; directly references DUT internals
module my_uart_rx8to8_sva;

  // Helpers
  function automatic bit valid_ctl (logic [2:0] c);
    return (c inside {3'h0,3'h1,3'h2,3'h3,3'h4,3'h5});
  endfunction

  function automatic logic [12:0] bps_thresh (logic [2:0] c);
    case (c)
      3'h0: bps_thresh = bps9600_2;
      3'h1: bps_thresh = bps19200_2;
      3'h2: bps_thresh = bps38400_2;
      3'h3: bps_thresh = bps57600_2;
      3'h4: bps_thresh = bps115200_2;
      3'h5: bps_thresh = bps256000_2;
      default: bps_thresh = 13'h0;
    endcase
  endfunction

  function automatic int unsigned bit_idx_from_tran (logic [4:0] t);
    return (t[4:1] - 1);
  endfunction

  // State encoding must be legal
  assert property (@(posedge clk) disable iff (!rst_n)
    state inside {IDLE, TRAN});

  // Reset effects
  assert property (@(posedge clk) !rst_n |-> (state==IDLE));
  assert property (@(posedge clk) !rst_n |-> (data_in=='0 && data_sign==0));

  // FSM transitions
  assert property (@(posedge clk) disable iff (!rst_n)
    (state==IDLE && !rs_rx) |=> (state==TRAN));
  assert property (@(posedge clk) disable iff (!rst_n)
    (state==IDLE && rs_rx) |=> (state==IDLE));
  assert property (@(posedge clk) disable iff (!rst_n)
    (state==TRAN && !recv_comp) |=> (state==TRAN));
  assert property (@(posedge clk) disable iff (!rst_n)
    (state==TRAN && recv_comp) |=> (state==IDLE));

  // Non-TRAN housekeeping
  assert property (@(posedge clk) disable iff (!rst_n)
    (state!=TRAN) |-> (cnt=='0 && tran_cnt=='0 && bps_sel==0 && sign_sel==0));

  // bps_sel pulse conditions
  assert property (@(posedge clk) disable iff (!rst_n)
    bps_sel |-> (state==TRAN && valid_ctl(uart_ctl) && cnt==bps_thresh(uart_ctl)));
  assert property (@(posedge clk) disable iff (!rst_n)
    bps_sel |=> !bps_sel); // one-cycle pulse

  // Counter behavior when uart_ctl is valid
  // Tick at threshold
  assert property (@(posedge clk) disable iff (!rst_n)
    (state==TRAN && valid_ctl(uart_ctl) && cnt==bps_thresh(uart_ctl))
      |=> (cnt=='0
           && tran_cnt==$past(tran_cnt)+1
           && bps_sel==~$past(sign_sel)
           && sign_sel==~$past(sign_sel)));

  // Count up otherwise
  assert property (@(posedge clk) disable iff (!rst_n)
    (state==TRAN && valid_ctl(uart_ctl) && cnt<bps_thresh(uart_ctl))
      |=> (cnt==$past(cnt)+1 && bps_sel==0
           && tran_cnt==$past(tran_cnt) && sign_sel==$past(sign_sel)));

  // Counter never overshoots selected threshold
  assert property (@(posedge clk) disable iff (!rst_n)
    (state==TRAN && valid_ctl(uart_ctl)) |-> (cnt<=bps_thresh(uart_ctl)));

  // Default (invalid uart_ctl) behavior inside TRAN
  assert property (@(posedge clk) disable iff (!rst_n)
    (state==TRAN && !valid_ctl(uart_ctl)) |-> (cnt=='0 && tran_cnt=='0 && bps_sel==0 && sign_sel==0));

  // tran_cnt range safety in TRAN (allowing one extra increment before IDLE)
  assert property (@(posedge clk) disable iff (!rst_n)
    (state==TRAN) |-> (tran_cnt<=5'd20));

  // data_sign correctness
  assert property (@(posedge clk) disable iff (!rst_n)
    data_sign |-> (bps_sel && (tran_cnt==5'd19)));
  assert property (@(posedge clk) disable iff (!rst_n)
    (!bps_sel || (tran_cnt!=5'd19)) |-> !data_sign);

  // Alignment of data_sign, recv_comp, and IDLE return
  // data_sign this cycle -> recv_comp next -> IDLE the cycle after
  assert property (@(posedge clk) disable iff (!rst_n)
    data_sign |=> (recv_comp) ##1 (state==IDLE));

  // Sampling of data bits: on valid sampling pulse, captured bit matches rs_rx of that cycle
  assert property (@(posedge clk) disable iff (!rst_n)
    (bps_sel && (tran_cnt>5'd2) && (tran_cnt<=5'd18))
      |-> (bit_idx_from_tran(tran_cnt) inside {[0:7]}));
  assert property (@(posedge clk) disable iff (!rst_n)
    (bps_sel && (tran_cnt>5'd2) && (tran_cnt<=5'd18))
      |=> (data_in[bit_idx_from_tran($past(tran_cnt))] == $past(rs_rx)));

  // Coverage: complete reception per baud selection
  // 8 sampling pulses within [4:18] followed by data_sign, then IDLE in two cycles
  sequence s_8_samples;
    (state==TRAN && bps_sel && (tran_cnt>=5'd4) && (tran_cnt<=5'd18))[->8];
  endsequence

  generate
    genvar gi;
    for (gi=0; gi<=5; gi++) begin : COV_PER_BAUD
      cover property (@(posedge clk) disable iff (!rst_n)
        (uart_ctl==gi && state==IDLE && rs_rx) ##1
        (state==IDLE && !rs_rx) ##1
        (state==TRAN) ##0 s_8_samples ##1 data_sign ##2 (state==IDLE));
    end
  endgenerate

  // Coverage: invalid uart_ctl observed during TRAN causes immediate clear
  cover property (@(posedge clk) disable iff (!rst_n)
    (state==TRAN && !valid_ctl(uart_ctl)) ##1 (cnt=='0 && tran_cnt=='0 && bps_sel==0 && sign_sel==0));

endmodule

bind my_uart_rx8to8 my_uart_rx8to8_sva sva_inst();