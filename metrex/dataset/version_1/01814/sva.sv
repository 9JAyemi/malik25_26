// SVA for rf_2p
// Bind-friendly, concise, and focuses on key behaviors.

module rf_2p_sva #(
  parameter int Word_Width = 32,
  parameter int Addr_Width = 8
)(
  input logic                      clka,
  input logic                      cena_i,
  input logic [Addr_Width-1:0]     addra_i,
  input logic [Word_Width-1:0]     dataa_o,

  input logic                      clkb,
  input logic                      cenb_i,
  input logic                      wenb_i,
  input logic [Addr_Width-1:0]     addrb_i,
  input logic [Word_Width-1:0]     datab_i,

  ref  logic [Word_Width-1:0]      mem_array [0:(1<<Addr_Width)-1]
);

  // A-port: data known when enabled; X when disabled (as coded).
  assert property (@(posedge clka) !cena_i |-> !$isunknown(dataa_o))
    else $error("A port: dataa_o has X/Z when enabled");

  assert property (@(posedge clka) cena_i |-> $isunknown(dataa_o))
    else $error("A port: dataa_o not X when disabled (model assigns 'bx)");

  // B-port: no write when CE is high.
  property B_NO_WRITE_WHEN_CE;
    logic [Addr_Width-1:0] a;
    logic [Word_Width-1:0] old;
    @(posedge clkb)
      (cenb_i, a = addrb_i, old = mem_array[addrb_i])
      |-> (mem_array[a] == old);
  endproperty
  assert property (B_NO_WRITE_WHEN_CE)
    else $error("B port: mem changed while cenb_i high");

  // B-port: unconditional write when wenb_i is low (active-low).
  property B_UNCOND_WRITE;
    logic [Addr_Width-1:0] a;
    logic [Word_Width-1:0] d;
    @(posedge clkb)
      (!cenb_i && !wenb_i, a = addrb_i, d = datab_i)
      |-> (mem_array[a] == d);
  endproperty
  assert property (B_UNCOND_WRITE)
    else $error("B port: unconditional write failed");

  // B-port: conditional max-write when wenb_i is high.
  // Guards against X in compare operands to avoid 4-state ambiguity.
  property B_MAX_WRITE_FUNCTIONAL;
    logic [Addr_Width-1:0] a;
    logic [Word_Width-1:0] d, old;
    @(posedge clkb)
      (!cenb_i && wenb_i && !$isunknown({datab_i, mem_array[addrb_i]}),
       a = addrb_i, d = datab_i, old = mem_array[addrb_i])
      |-> (mem_array[a] == ((d > old) ? d : old));
  endproperty
  assert property (B_MAX_WRITE_FUNCTIONAL)
    else $error("B port: max-write behavior incorrect");

  // B-port: under max-mode, value never decreases.
  property B_MAX_MODE_NONDECREASING;
    logic [Addr_Width-1:0] a;
    logic [Word_Width-1:0] old;
    @(posedge clkb)
      (!cenb_i && wenb_i && !$isunknown(mem_array[addrb_i]),
       a = addrb_i, old = mem_array[addrb_i])
      |-> (mem_array[a] >= old);
  endproperty
  assert property (B_MAX_MODE_NONDECREASING)
    else $error("B port: value decreased in max mode");

  // Coverage
  cover property (@(posedge clkb) cenb_i);
  cover property (@(posedge clkb) !cenb_i && !wenb_i);

  cover property (@(posedge clkb)
    !cenb_i && wenb_i && !$isunknown({datab_i, mem_array[addrb_i]}) &&
    (datab_i >  mem_array[addrb_i]));  // max-taken

  cover property (@(posedge clkb)
    !cenb_i && wenb_i && !$isunknown({datab_i, mem_array[addrb_i]}) &&
    (datab_i <= mem_array[addrb_i]));  // max-not-taken

  cover property (@(posedge clka) !cena_i); // A-port read enable

  // Cross-domain coverage: B write followed by A read of same address.
  property C_READ_AFTER_WRITE_SAME_ADDR;
    logic [Addr_Width-1:0] a;
    @(posedge clkb)
      (!cenb_i, a = addrb_i)
      ##[1:$] @(posedge clka) (!cena_i && addra_i == a);
  endproperty
  cover property (C_READ_AFTER_WRITE_SAME_ADDR);

  // Optional: simultaneous A read and B write to same address in same timestep.
  cover property (@(posedge clkb)
    !cenb_i ##0 @(posedge clka) (!cena_i && (addra_i == addrb_i)));

endmodule

// Example bind (place in a separate file or TB):
// bind rf_2p rf_2p_sva #(.Word_Width(Word_Width), .Addr_Width(Addr_Width))
//   rf_2p_sva_i (.* , .mem_array(mem_array));