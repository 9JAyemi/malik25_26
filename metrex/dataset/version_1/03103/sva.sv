// SVA for instr_buffer
// Bindable, concise, high-value checks

// 1) Port-level checker (bind to verify handshake, tags, stability, ranges)
module instr_buffer_sva
  #(parameter int NUMOFCU = 1)
(
  input  logic                         clk,
  input  logic                         rst,
  input  logic [NUMOFCU-1:0]           fetch_rd_en,
  input  logic [NUMOFCU*32-1:0]        fetch_addr,
  input  logic [NUMOFCU*39-1:0]        fetch_tag,
  input  logic [NUMOFCU-1:0]           fetchwave_ack,
  input  logic [NUMOFCU*32-1:0]        wave_instr,
  input  logic [NUMOFCU*39-1:0]        wave_tag
);

  // Default clocking for brevity
  default clocking cb @(posedge clk); endclocking

  // Helper to slice per-CU fields
  function automatic logic [31:0] addr_i (int i);
    return fetch_addr[i*32 +: 32];
  endfunction
  function automatic logic [38:0] ftag_i (int i);
    return fetch_tag[i*39 +: 39];
  endfunction
  function automatic logic [31:0] winstr_i (int i);
    return wave_instr[i*32 +: 32];
  endfunction
  function automatic logic [38:0] wtag_i (int i);
    return wave_tag[i*39 +: 39];
  endfunction

  genvar gi;
  generate
    for (gi = 0; gi < NUMOFCU; gi++) begin : g

      // Exact ack behavior
      assert property (fetchwave_ack[gi] == (~rst & fetch_rd_en[gi]))
        else $error("ACK mismatch CU%0d", gi);

      // Tag pass-through when ack; tag must be X when no ack
      assert property (fetchwave_ack[gi] |-> (wtag_i(gi) == ftag_i(gi)))
        else $error("Tag mismatch on ACK CU%0d", gi);
      assert property (!fetchwave_ack[gi] |-> $isunknown(wtag_i(gi)))
        else $error("Tag not X when no ACK CU%0d", gi);

      // Data known when ack
      assert property (fetchwave_ack[gi] |-> (!$isunknown(winstr_i(gi)) && !$isunknown(ftag_i(gi))))
        else $error("Data/tag unknown on ACK CU%0d", gi);

      // No spurious data writes: when no ack, data holds its previous value
      assert property (disable iff (rst) !fetchwave_ack[gi] |-> (winstr_i(gi) == $past(winstr_i(gi))))
        else $error("Data changed without ACK CU%0d", gi);

      // Legal address range when ack (memory depth 10000, need base..base+3 in range)
      assert property (fetchwave_ack[gi] |-> (addr_i(gi) <= 32'd9997))
        else $error("Address out of range on ACK CU%0d", gi);

      // Basic functional coverage
      cover property (fetchwave_ack[gi]);
      cover property (fetchwave_ack[gi] ##1 fetchwave_ack[gi]);                 // back-to-back reads
      cover property (fetchwave_ack[gi] && (addr_i(gi) == 32'd0));              // low boundary
      cover property (fetchwave_ack[gi] && (addr_i(gi) == 32'd9997));           // high boundary

    end
  endgenerate

endmodule

// Bind this checker to the DUT
bind instr_buffer instr_buffer_sva #(.NUMOFCU(NUMOFCU)) u_instr_buffer_sva (
  .clk(clk),
  .rst(rst),
  .fetch_rd_en(fetch_rd_en),
  .fetch_addr(fetch_addr),
  .fetch_tag(fetch_tag),
  .fetchwave_ack(fetchwave_ack),
  .wave_instr(wave_instr),
  .wave_tag(wave_tag)
);

// 2) Internal memory content checker (binds into DUT scope; verifies byte-lane mapping).
// Requires access to instr_memory inside instr_buffer via bind of a checker.
checker ib_memmap_chk #(parameter int NUMOFCU = 1);
  default clocking cb @(posedge clk); endclocking
  genvar gi;
  generate
    for (gi = 0; gi < NUMOFCU; gi++) begin : g
      // Local slices from DUT scope
      wire [31:0] a   = fetch_addr[gi*32 +: 32];
      wire        ack = fetchwave_ack[gi];
      wire [31:0] d   = wave_instr[gi*32 +: 32];

      // When ack and address legal, data must equal 4 consecutive bytes: {+3,+2,+1,+0}
      assert property (ack && (a <= 32'd9997) |-> (d == {instr_memory[a+3], instr_memory[a+2], instr_memory[a+1], instr_memory[a+0]}))
        else $error("Byte-lane/data mismatch CU%0d", gi);

      // Cover a few representative addresses if they occur
      cover property (ack && (a inside {32'd0, 32'd1, 32'd9996, 32'd9997}));
    end
  endgenerate
endchecker

// Bind internal checker (tools that support bind of checker into module scope)
bind instr_buffer ib_memmap_chk #(.NUMOFCU(NUMOFCU)) u_ib_memmap_chk;