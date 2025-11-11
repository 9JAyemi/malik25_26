// SVA checker for simple_ram
module simple_ram_sva
  #(parameter width=1, parameter widthad=1)
  (input clk,
   input [widthad-1:0] wraddress,
   input               wren,
   input [width-1:0]   data,
   input [widthad-1:0] rdaddress,
   input [width-1:0]   q);

  bit past_valid;
  always @(posedge clk) past_valid <= 1'b1;

  default clocking cb @(posedge clk); endclocking

  // Read is 1-cycle latency, returns prior mem value at rdaddress
  property p_read_latency;
    disable iff (!past_valid)
    q == $past(mem[rdaddress]);
  endproperty
  assert property (p_read_latency);

  // Memory semantics per address: only write modifies it; value written matches data
  genvar a;
  generate
    for (a = 0; a < (1<<widthad); a++) begin : G_ADDR
      // Location a updates to past data on a write hit
      property p_write_update;
        disable iff (!past_valid)
        (wren && wraddress == a) |=> (mem[a] == $past(data));
      endproperty
      assert property (p_write_update);

      // Location a holds when not written
      property p_hold_when_no_write;
        disable iff (!past_valid)
        !(wren && (wraddress == a)) |=> (mem[a] == $past(mem[a]));
      endproperty
      assert property (p_hold_when_no_write);
    end
  endgenerate

  // Key scenario coverage
  // Any write
  cover property (@(posedge clk) wren);
  // Read-after-write (next cycle) returns written data
  cover property (@(posedge clk) past_valid && wren ##1 (rdaddress == $past(wraddress)) && (q == $past(data)));
  // Same-cycle read/write to same address (collision) shows old data on q
  cover property (@(posedge clk) past_valid && wren && (rdaddress == wraddress));

endmodule

// Bind into the DUT to access internal mem
bind simple_ram simple_ram_sva #(.width(width), .widthad(widthad))
  simple_ram_sva_i (.*);