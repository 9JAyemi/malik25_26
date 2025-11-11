// SVA for fifo_24in_24out_12kb_compare_0
// Focused, high-value checks and coverage

module fifo_24in_24out_12kb_compare_0_sva ();

  // Mirror DUT constants (locals are not externally visible)
  localparam int WIDTH       = 24;
  localparam int DEPTH       = 512;
  localparam int ADDR_WIDTH  = 9;
  localparam int FULL_ADDR   = DEPTH-1;
  localparam int EMPTY_ADDR  = 0;
  localparam int COMP_OFFSET = 24;

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Reset behavior (not disabled during reset)
  assert property (disable iff (1'b0) @(posedge clk)
                   rst |-> (write_ptr==EMPTY_ADDR && read_ptr==EMPTY_ADDR && dout=='0 && comp==1'b0));

  // Pointer in-range (safety)
  assert property (write_ptr <= FULL_ADDR && read_ptr <= FULL_ADDR);

  // Flags cannot be both asserted
  assert property (!(full && empty));

  // Write pointer update and hold
  assert property (!full  |-> ##1 (write_ptr == (($past(write_ptr)==FULL_ADDR) ? EMPTY_ADDR : $past(write_ptr)+1)));
  assert property ( full  |-> ##1 (write_ptr == $past(write_ptr)));

  // Read pointer update and hold
  assert property (!empty |-> ##1 (read_ptr == (($past(read_ptr)==FULL_ADDR) ? EMPTY_ADDR : $past(read_ptr)+1)));
  assert property ( empty |-> ##1 (read_ptr == $past(read_ptr)));

  // Memory write occurs only when !full, to the expected address
  assert property (!full |-> ##1 fifo[$past(write_ptr)] == $past(din));

  // No memory write when full (location pointed to by write_ptr remains stable)
  assert property ( full |-> ##1 fifo[$past(write_ptr)] == $past(fifo[$past(write_ptr)]));

  // dout update semantics
  assert property (!empty |-> ##1 dout == $past(read_data));
  assert property ( empty |-> ##1 dout == $past(dout));

  // comp update semantics (uses previous-cycle comp_data and dout)
  assert property (1'b1 |-> ##1 comp == $past(comp_data == dout));

  // Basic functional coverages
  cover property (rst);
  cover property (!full && !empty);                   // simultaneous read/write
  cover property (full ##1 !full);                    // full deasserts
  cover property (empty ##1 !empty);                  // empty deasserts
  cover property (!full  && write_ptr==FULL_ADDR ##1 write_ptr==EMPTY_ADDR);  // write_ptr wrap
  cover property (!empty && read_ptr ==FULL_ADDR ##1 read_ptr ==EMPTY_ADDR);  // read_ptr wrap
  cover property (!empty && (read_ptr <  COMP_OFFSET));  // comp_data zero-side
  cover property (!empty && (read_ptr >= COMP_OFFSET));  // comp_data fifo-side
  cover property (comp);
  cover property (!comp);

endmodule

bind fifo_24in_24out_12kb_compare_0 fifo_24in_24out_12kb_compare_0_sva sva_inst();