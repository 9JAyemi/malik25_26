// SVA checker for fifo_generator
module fifo_generator_sva #(
  parameter int AW    = 6,
  parameter int DW    = 94,
  parameter int DEPTH = 256
)(
  input  logic                 clk,
  input  logic                 ENB,
  input  logic [0:0]           E,
  input  logic [0:0]           Q,
  input  logic [AW-1:0]        ADDRB,
  input  logic [AW-1:0]        ADDRA,
  input  logic [DW-1:0]        din,
  input  logic [DW-1:0]        DOUTB,
  // import the DUT memory (unpacked) so we can assert its behavior
  input  logic [DW-1:0]        mem [0:DEPTH-1]
);

  default clocking cb @(posedge clk); endclocking

  // allow $past usage after first edge
  logic past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge clk) past_valid <= 1'b1;
  default disable iff (!past_valid)

  // Basic sanitation
  assert property ( !$isunknown({ENB,E,Q,ADDRA,ADDRB}) )
    else $error("X/Z on control/address");

  // Address range used must be within memory depth
  assert property ( (ADDRA < DEPTH) && (ADDRB < DEPTH) )
    else $error("Address out of range");

  // DOUTB must mirror mem[ADDRB] combinationally (sampled each clk)
  assert property ( DOUTB === mem[ADDRB] )
    else $error("DOUTB != mem[ADDRB]");

  // No simultaneous double-write to the same location
  assert property ( !(E && ENB && (ADDRA == ADDRB)) )
    else $error("Simultaneous writes to same address");

  // Write-port A behavior: on E, mem[ADDRA] captures din
  assert property ( E |-> mem[$past(ADDRA)] == $past(din) )
    else $error("Write-port A data mismatch");

  // Shift-port B boundary safety
  assert property ( (ENB &&  Q) |-> (ADDRB < DEPTH-1) )
    else $error("Shift up overflows source index");
  assert property ( (ENB && !Q) |-> (ADDRB > 0) )
    else $error("Shift down underflows source index");

  // Shift-port B data movement (uses prior-cycle source)
  assert property ( (ENB &&  Q && (ADDRB < DEPTH-1))
                    |-> mem[$past(ADDRB)] == $past(mem[ADDRB+1]) )
    else $error("Shift up data mismatch");
  assert property ( (ENB && !Q && (ADDRB > 0))
                    |-> mem[$past(ADDRB)] == $past(mem[ADDRB-1]) )
    else $error("Shift down data mismatch");

  // Functional coverage
  cover property ( E );
  cover property ( ENB &&  Q );
  cover property ( ENB && !Q );
  cover property ( ENB &&  Q && (ADDRB == (DEPTH-2)) ); // near top boundary
  cover property ( ENB && !Q && (ADDRB == 1) );         // near bottom boundary

endmodule

// Bind the checker to the DUT
bind fifo_generator fifo_generator_sva #(
  .AW(6), .DW(94), .DEPTH(256)
) fifo_generator_sva_i (
  .clk   (clk),
  .ENB   (ENB),
  .E     (E),
  .Q     (Q),
  .ADDRB (ADDRB),
  .ADDRA (ADDRA),
  .din   (din),
  .DOUTB (DOUTB),
  .mem   (mem)
);