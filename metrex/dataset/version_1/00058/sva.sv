// SVA for rw_manager_ram
// Concise, high-quality checks with a minimal scoreboard model

module rw_manager_ram_sva
  #(parameter DATA_WIDTH=36, ADDR_WIDTH=8)
(
  input  logic                         clock,
  input  logic                         wren,
  input  logic [ADDR_WIDTH-1:0]        rdaddress,
  input  logic [ADDR_WIDTH-1:0]        wraddress,
  input  logic [DATA_WIDTH-1:0]        data,
  input  logic [DATA_WIDTH-1:0]        q
);

  default clocking cb @(posedge clock); endclocking

  // Shadow memory of prior-cycle DUT state; valid-bit per address
  logic [DATA_WIDTH-1:0] ref_mem [0:(1<<ADDR_WIDTH)-1];
  logic [(1<<ADDR_WIDTH)-1:0] init;

  // Update model after sampling (NBA), matching DUT semantics
  always_ff @(posedge clock) begin
    if (wren && !$isunknown({wraddress, data})) begin
      ref_mem[wraddress] <= data;
      init[wraddress]    <= 1'b1;
    end
  end

  // Basic input X/Z checks
  a_inputs_known: assert property ( !$isunknown({wren, rdaddress, wraddress}) )
    else $error("rw_manager_ram: control/address has X/Z");

  a_data_known_on_write: assert property ( wren |-> !$isunknown(data) )
    else $error("rw_manager_ram: data X/Z when wren=1");

  // Core functional check: synchronous read returns prior-cycle memory at current rdaddress.
  // Skip until that location is initialized at least once.
  a_q_matches_model: assert property ( (init[rdaddress] && !$isunknown(rdaddress)) |-> (q == ref_mem[rdaddress]) )
    else $error("rw_manager_ram: q mismatch vs model at rdaddress=%0d", rdaddress);

  // Optional stronger check: next-cycle readback of a write
  a_next_cycle_readback: assert property (
      (wren && !$isunknown({wraddress, data}))
      ##1 (rdaddress == $past(wraddress)) |-> (q == $past(data))
    ) else $error("rw_manager_ram: next-cycle readback mismatch");

  // Corner-case: same-cycle read & write to same address returns old data
  a_same_cycle_rw_old_data: assert property (
      (wren && (wraddress == rdaddress) && init[rdaddress]) |-> (q == ref_mem[rdaddress])
    ) else $error("rw_manager_ram: same-cycle RW old-data violation");

  // Coverage
  c_write:                cover property ( wren );
  c_read_init:            cover property ( init[rdaddress] && !wren );
  c_rw_same_addr:         cover property ( wren && (wraddress == rdaddress) );
  c_rw_diff_addr:         cover property ( wren && (wraddress != rdaddress) );
  c_back_to_back_writes:  cover property ( wren ##1 wren );
  c_read_after_write:     cover property ( (wren, logic [ADDR_WIDTH-1:0] A = wraddress) ##1 (rdaddress == A) );

endmodule

// Bind into DUT
bind rw_manager_ram rw_manager_ram_sva #(.DATA_WIDTH(DATA_WIDTH), .ADDR_WIDTH(ADDR_WIDTH)) u_rw_manager_ram_sva
(
  .clock(clock),
  .wren(wren),
  .rdaddress(rdaddress),
  .wraddress(wraddress),
  .data(data),
  .q(q)
);