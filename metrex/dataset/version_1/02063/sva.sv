// SVA checker for afifo_sram
// Bind this checker to the DUT to verify pointers, flags, ordering, and coverage.

module afifo_sram_sva #(
  parameter DEPTH = 256,
  parameter ADDRESS_WIDTH = 8,
  parameter WIDTH = 8
)(
  input  logic                    CLK,
  input  logic                    RESET,
  input  logic                    REN,
  input  logic                    WEN,
  input  logic                    valid_in,
  input  logic [WIDTH-1:0]        Data_in,
  input  logic [WIDTH-1:0]        Data_out,
  input  logic                    Full_out,
  input  logic                    Empty_out,
  // internal DUT nets
  input  logic [ADDRESS_WIDTH-1:0] read_ptr,
  input  logic [ADDRESS_WIDTH-1:0] write_ptr,
  input  logic [ADDRESS_WIDTH-1:0] next_write_ptr,
  input  logic [ADDRESS_WIDTH-1:0] next_read_ptr,
  input  logic [ADDRESS_WIDTH-1:0] mem_addr
);

  default clocking cb @(posedge CLK); endclocking
  default disable iff (RESET);

  // Handshake events (as implemented by DUT gating)
  logic do_write, do_read;
  assign do_write = WEN && !Full_out;
  assign do_read  = REN && !Empty_out && valid_in;

  // Basic sanity: reset behavior (synchronous)
  assert property (@(posedge CLK) RESET |=> (read_ptr==0 && write_ptr==0));

  // Next pointer combinational correctness
  assert property ((write_ptr == DEPTH-1) |-> (next_write_ptr == 0));
  assert property ((write_ptr != DEPTH-1) |-> (next_write_ptr == write_ptr + 1));
  assert property ((read_ptr  == DEPTH-1) |-> (next_read_ptr  == 0));
  assert property ((read_ptr  != DEPTH-1) |-> (next_read_ptr  == read_ptr  + 1));

  // Mem address muxing
  assert property ( REN |-> (mem_addr == read_ptr));
  assert property (!REN |-> (mem_addr == write_ptr));

  // Pointers only advance when their operation is performed; otherwise hold
  assert property ( do_write |=> (write_ptr == $past(next_write_ptr)));
  assert property (!do_write |=> (write_ptr == $past(write_ptr)));
  assert property ( do_read  |=> (read_ptr  == $past(next_read_ptr)));
  assert property (!do_read  |=> (read_ptr  == $past(read_ptr)));

  // Blocked operations must not change pointers
  assert property ((WEN &&  Full_out)                       |=> $stable(write_ptr));
  assert property ((REN && (Empty_out || !valid_in))        |=> $stable(read_ptr));

  // Flag definitions and sanity
  assert property ( Full_out  == ((next_write_ptr == read_ptr) && !REN));
  assert property ( Empty_out == ((write_ptr     == read_ptr) && !WEN));
  assert property (!(Full_out && Empty_out)); // mutual exclusion

  // Lightweight occupancy model (one-slot-empty). Range: 0..DEPTH-1
  int unsigned occ;
  // Model updates
  always_ff @(posedge CLK) begin
    if (RESET) begin
      occ <= 0;
    end else begin
      unique case ({do_write, do_read})
        2'b10: if (occ < DEPTH-1) occ <= occ + 1;
        2'b01: if (occ > 0)       occ <= occ - 1;
        default:                  occ <= occ;
      endcase
    end
  end

  // Occupancy in-range
  assert property (occ <= DEPTH-1);

  // Occupancy vs pointers (one-slot-empty scheme)
  assert property ((occ == 0) <-> (write_ptr == read_ptr));
  assert property ((occ == DEPTH-1) <-> (next_write_ptr == read_ptr));

  // Flags vs occupancy (including REN/WEN gating semantics in DUT)
  assert property (((occ == 0)         && !WEN) |->  Empty_out);
  assert property ( (occ != 0)                    |-> !Empty_out);
  assert property (((occ == DEPTH-1)   && !REN) |->  Full_out);
  assert property ( (occ != DEPTH-1)              |-> !Full_out);
  assert property (((occ == 0)         &&  WEN) |-> !Empty_out);
  assert property (((occ == DEPTH-1)   &&  REN) |-> !Full_out);

  // No underflow/overflow at handshake level
  assert property (!((occ == 0)         && do_read));
  assert property (!((occ == DEPTH-1)   && do_write && !do_read));

  // FIFO data ordering using a scoreboard
  bit [WIDTH-1:0] q[$];
  always_ff @(posedge CLK) begin
    if (RESET) begin
      q.delete();
    end else begin
      // Push on successful write
      if (do_write) q.push_back(Data_in);

      // Check and pop on successful read
      if (do_read) begin
        assert (q.size() > 0) else $error("Underflow: read when scoreboard empty");
        if (q.size() > 0) begin
          assert (Data_out === q[0]) else $error("FIFO ordering/data mismatch");
          q.pop_front();
        end
      end
    end
  end

  // Coverage: wrap, full/empty transitions, simultaneous R/W, bypass cases
  cover property (1'b1 ##1 do_write [* (DEPTH+1)] ##1 (write_ptr == 0)); // write wrap
  cover property (1'b1 ##1 do_read  [* (DEPTH+1)] ##1 (read_ptr  == 0)); // read wrap
  cover property ((occ == 0) ##1 do_write ##1 (occ > 0) ##1 do_read ##1 (occ == 0)); // empty->nonempty->empty
  cover property ((occ == DEPTH-2) ##1 (do_write && do_read)); // simultaneous near-full
  cover property ((occ == 0) && WEN && REN && valid_in); // empty + write enables read-bypass
  cover property ((occ == DEPTH-1) && REN && WEN && valid_in); // full-1 with simultaneous R/W

endmodule

// Example bind (place in a testbench or a separate bind file):
// bind afifo_sram afifo_sram_sva #(.DEPTH(DEPTH), .ADDRESS_WIDTH(ADDRESS_WIDTH), .WIDTH(WIDTH))
// ( .CLK(CLK), .RESET(RESET), .REN(REN), .WEN(WEN), .valid_in(valid_in),
//   .Data_in(Data_in), .Data_out(Data_out), .Full_out(Full_out), .Empty_out(Empty_out),
//   .read_ptr(read_ptr), .write_ptr(write_ptr), .next_write_ptr(next_write_ptr),
//   .next_read_ptr(next_read_ptr), .mem_addr(mem_addr) );