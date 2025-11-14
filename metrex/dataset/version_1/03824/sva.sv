// SVA for nkmd_dai_rx and nkmd_dai_tx
// Concise, high-value checks + minimal functional coverage
// Bind these modules to the DUTs

// ---------------- RX ----------------
module nkmd_dai_rx_sva(
  input wire clk, rst,
  input wire [23:0] rx_data_i,
  input wire rx_ack_i,
  input wire [31:0] data_i,
  input wire [31:0] data_o,
  input wire [31:0] addr_i,
  input wire we_i,
  input wire [5:0] nextw_ff,
  input wire [5:0] unread_ff,
  input wire [5:0] shift_ff
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Reference ring buffer model (shadow)
  logic [23:0] rb_ref [0:63];
  always_ff @(posedge clk) begin
    if (rst) begin
      // no need to clear rb_ref
    end else if (rx_ack_i) begin
      rb_ref[nextw_ff] <= rx_data_i;
    end
  end

  // Decodes
  wire addrF   = addr_i[15:12] == 4'hf;
  wire addrD00 = (addr_i[15:12] == 4'hd) && (addr_i[7:0] == 8'h00);
  wire [5:0] offset_i = addr_i[5:0];
  wire should_shift = we_i && addrD00;

  // Reset values
  assert property (rst |-> nextw_ff == 6'd0);
  assert property (rst |-> unread_ff == 6'd0);
  assert property (rst |-> shift_ff  == 6'd0);

  // Write pointer behavior
  assert property (!rst && rx_ack_i  |-> nextw_ff == $past(nextw_ff) + 6'd1)
    else $error("RX nextw_ff did not increment on rx_ack_i");
  assert property (!rst && !rx_ack_i |-> nextw_ff == $past(nextw_ff))
    else $error("RX nextw_ff changed without rx_ack_i");

  // unread_ff / shift_ff state machine
  // should_shift && !rx_ack_i: unread--, shift++
  assert property (!rst && $past(should_shift) && !$past(rx_ack_i)
                   |-> unread_ff == $past(unread_ff) - 6'd1 && shift_ff == $past(shift_ff) + 6'd1)
    else $error("RX unread/shift wrong: shift only case");
  // !should_shift && rx_ack_i: unread++, shift holds
  assert property (!rst && !$past(should_shift) && $past(rx_ack_i)
                   |-> unread_ff == $past(unread_ff) + 6'd1 && shift_ff == $past(shift_ff))
    else $error("RX unread/shift wrong: ack only case");
  // should_shift && rx_ack_i: shift++, unread holds
  assert property (!rst && $past(should_shift) && $past(rx_ack_i)
                   |-> unread_ff == $past(unread_ff) && shift_ff == $past(shift_ff) + 6'd1)
    else $error("RX unread/shift wrong: both case");
  // neither: both hold
  assert property (!rst && !$past(should_shift) && !$past(rx_ack_i)
                   |-> unread_ff == $past(unread_ff) && shift_ff == $past(shift_ff))
    else $error("RX unread/shift wrong: idle case");

  // No underflow on explicit decrement path
  assert property (!rst && $past(should_shift) && !$past(rx_ack_i) |-> $past(unread_ff) > 0)
    else $error("RX unread underflow on shift");

  // Data output mapping (1-cycle latency)
  assert property ($past(addrF) |-> data_o == $past(rb_ref[$past(shift_ff) + $past(offset_i)]))
    else $error("RX data_o mismatch for addr F read");
  assert property ($past(addrD00) |-> data_o == $past(unread_ff))
    else $error("RX data_o unread counter mismatch");
  assert property (!$past(addrF) && !$past(addrD00) |-> data_o == 32'd0)
    else $error("RX data_o should be 0 for other addresses");

  // Functional coverage (key scenarios)
  cover property (rx_ack_i && !should_shift);
  cover property (!rx_ack_i && should_shift);
  cover property (rx_ack_i && should_shift);
  cover property (rx_ack_i && $past(nextw_ff) == 6'h3f); // write pointer wrap
  cover property (should_shift && $past(shift_ff) == 6'h3f); // shift wrap
endmodule

bind nkmd_dai_rx nkmd_dai_rx_sva rx_sva_bind(
  .clk(clk), .rst(rst),
  .rx_data_i(rx_data_i),
  .rx_ack_i(rx_ack_i),
  .data_i(data_i),
  .data_o(data_o),
  .addr_i(addr_i),
  .we_i(we_i),
  .nextw_ff(nextw_ff),
  .unread_ff(unread_ff),
  .shift_ff(shift_ff)
);

// ---------------- TX ----------------
module nkmd_dai_tx_sva(
  input wire clk, rst,
  input wire [23:0] tx_data_o,
  input wire tx_pop_i,
  input wire tx_ack_o,
  input wire [31:0] data_i,
  input wire [31:0] data_o,
  input wire [31:0] addr_i,
  input wire we_i,
  input wire [5:0] queued_ff,
  input wire [5:0] lastr_ff,
  input wire [5:0] nextw_ff
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Reference ring buffer model
  logic [23:0] rb_ref [0:63];

  // Decodes
  wire addrE   = addr_i[15:12] == 4'he;
  wire addrD01 = (addr_i[15:12] == 4'hd) && (addr_i[7:0] == 8'h01);
  wire [5:0] offset_i = addr_i[5:0];
  wire should_queue = we_i && addrD01;

  // Shadow memory update (on enqueue)
  always_ff @(posedge clk) begin
    if (!rst) begin
      if (should_queue) rb_ref[nextw_ff] <= data_i[23:0];
    end
  end

  // Reset values
  assert property (rst |-> queued_ff == 6'd0);
  assert property (rst |-> lastr_ff  == 6'h3f);
  assert property (rst |-> nextw_ff  == 6'd0);

  // tx_ack_o is registered copy of tx_pop_i
  assert property (!rst |-> tx_ack_o == $past(tx_pop_i))
    else $error("TX ack not equal to delayed pop");

  // Queue accounting across all cases
  // Enqueue only
  assert property (!rst && $past(should_queue) && !$past(tx_pop_i)
                   |-> queued_ff == $past(queued_ff) + 6'd1
                    && nextw_ff == $past(nextw_ff) + 6'd1
                    && lastr_ff == $past(lastr_ff))
    else $error("TX enqueue-only accounting error");
  // Dequeue only
  assert property (!rst && !$past(should_queue) && $past(tx_pop_i) && $past(queued_ff) > 0
                   |-> queued_ff == $past(queued_ff) - 6'd1
                    && lastr_ff == $past(lastr_ff) + 6'd1)
    else $error("TX dequeue-only accounting error when non-empty");
  assert property (!rst && !$past(should_queue) && $past(tx_pop_i) && $past(queued_ff) == 0
                   |-> queued_ff == $past(queued_ff)
                    && lastr_ff == $past(lastr_ff))
    else $error("TX dequeue attempted on empty should not change state");
  // Enqueue + Dequeue in same cycle
  assert property (!rst && $past(should_queue) && $past(tx_pop_i) && $past(queued_ff) > 0
                   |-> queued_ff == $past(queued_ff)
                    && lastr_ff == $past(lastr_ff) + 6'd1
                    && nextw_ff == $past(nextw_ff) + 6'd1)
    else $error("TX both case accounting error (non-empty)");
  assert property (!rst && $past(should_queue) && $past(tx_pop_i) && $past(queued_ff) == 0
                   |-> queued_ff == $past(queued_ff) + 6'd1
                    && lastr_ff == $past(lastr_ff)
                    && nextw_ff == $past(nextw_ff) + 6'd1)
    else $error("TX both case accounting error (empty)");

  // Optional invariant: queued == nextw - lastr - 1 (check after NBA via ##0)
  assert property (1'b1 |-> ##0 (queued_ff == (nextw_ff - lastr_ff - 6'd1)))
    else $error("TX invariant broken: queued != nextw - lastr - 1");

  // Data output mapping (1-cycle latency for MMIO reads)
  assert property ($past(addrE)   |-> data_o == $past(rb_ref[$past(nextw_ff) - 6'd1 - $past(offset_i)]))
    else $error("TX data_o mismatch for addr E read");
  assert property ($past(addrD01) |-> data_o == $past(queued_ff))
    else $error("TX data_o queued counter mismatch");
  assert property (!$past(addrE) && !$past(addrD01) |-> data_o == 32'd0)
    else $error("TX data_o should be 0 for other addresses");

  // tx_data_o should reflect current head element (after NBA) — use ##0
  assert property (1'b1 |-> ##0 (tx_data_o == rb_ref[lastr_ff]))
    else $error("TX tx_data_o not equal to rb_ref[lastr_ff]");

  // Functional coverage
  cover property (should_queue && !tx_pop_i);
  cover property (!should_queue && tx_pop_i && queued_ff != 0);
  cover property (should_queue && tx_pop_i && queued_ff != 0);
  cover property (should_queue && tx_pop_i && queued_ff == 0);
  cover property ($past(nextw_ff) == 6'h3f && should_queue); // write pointer wrap
  cover property ($past(lastr_ff) == 6'h3f && tx_pop_i && $past(queued_ff)>0); // read pointer wrap
endmodule

bind nkmd_dai_tx nkmd_dai_tx_sva tx_sva_bind(
  .clk(clk), .rst(rst),
  .tx_data_o(tx_data_o),
  .tx_pop_i(tx_pop_i),
  .tx_ack_o(tx_ack_o),
  .data_i(data_i),
  .data_o(data_o),
  .addr_i(addr_i),
  .we_i(we_i),
  .queued_ff(queued_ff),
  .lastr_ff(lastr_ff),
  .nextw_ff(nextw_ff)
);