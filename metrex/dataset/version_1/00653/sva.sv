// SVA checker for ram_dp_8x512
module ram_dp_8x512_sva (
  input        clock_a,
  input        wren_a,
  input  [8:0] address_a,
  input  [7:0] data_a,
  input        clock_b,
  input        wren_b,
  input  [8:0] address_b,
  input  [7:0] data_b,
  input  [7:0] q_a,
  input  [7:0] q_b
);
  // Reference model (atomic single-writer on clock_a)
  logic [7:0] ref_mem [0:511];
  logic [8:0] last_wr_addr;
  logic [7:0] last_wr_data;

  // Update reference memory on Port A writes
  always_ff @(posedge clock_a) begin
    if (wren_a) begin
      ref_mem[address_a] <= data_a;
      last_wr_addr       <= address_a;
      last_wr_data       <= data_a;
    end
  end

  // Basic input sanity (no X/Z, in-range)
  assert property (@(posedge clock_a) !$isunknown({wren_a, address_a, data_a}));
  assert property (@(posedge clock_b) !$isunknown({wren_b, address_b, data_b}));
  assert property (@(posedge clock_a) address_a < 512);
  assert property (@(posedge clock_b) address_b < 512);

  // Port A functional correctness: registered read of current address sees "old" data
  assert property (@(posedge clock_a) q_a === ref_mem[address_a]);
  // If ref data is known, q_a must be known
  assert property (@(posedge clock_a) $isunknown(ref_mem[address_a]) || !$isunknown(q_a));

  // Port B functional correctness: registered read of current address reflects last A-write
  assert property (@(posedge clock_b) q_b === ref_mem[address_b]);
  // If ref data is known, q_b must be known
  assert property (@(posedge clock_b) $isunknown(ref_mem[address_b]) || !$isunknown(q_b));

  // Latency/read-during-write semantics on A:
  // If address is held and we write, next A cycle q_a equals the written data
  assert property (@(posedge clock_a)
                   wren_a && $stable(address_a) |-> ##1 (q_a === $past(data_a)));

  // Port B has no write path in DUT: flag any use of wren_b
  assert property (@(posedge clock_b) wren_b == 1'b0)
    else $error("wren_b is unused by DUT and must remain 0");

  // Coverage
  // Exercise A writes
  cover property (@(posedge clock_a) wren_a);
  // Exercise A write followed by A readback (same address held)
  cover property (@(posedge clock_a)
                  wren_a && $stable(address_a) ##1 (q_a === $past(data_a)));
  // Exercise B observing latest A write
  cover property (@(posedge clock_b)
                  (address_b == last_wr_addr) && (q_b === last_wr_data));
endmodule

// Bind into DUT
bind ram_dp_8x512 ram_dp_8x512_sva u_ram_dp_8x512_sva (.*);