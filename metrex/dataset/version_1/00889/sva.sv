// SVA checker for my_memory. Bind this to the DUT.
module my_memory_sva (
  input  logic         clka,
  input  logic [15:0]  addra,
  input  logic [11:0]  douta,
  input  logic         ena,
  input  logic         regcea,
  input  logic         wea,
  input  logic [11:0]  dina,
  input  logic         rst
);

  // basic clock/past gating
  logic past_valid;
  always_ff @(posedge clka or posedge rst) begin
    if (rst) past_valid <= 1'b0;
    else     past_valid <= 1'b1;
  end

  default clocking cb @(posedge clka); endclocking
  default disable iff (!past_valid);

  // helpers
  function automatic bit in_range_addr (logic [15:0] a);
    return (!$isunknown(a) && a <= 16'd256);
  endfunction

  // shadow model (only for checked, in-range writes)
  logic [11:0] shadow_mem [0:256];
  bit          written    [0:256];

  // maintain shadow state
  integer i;
  always_ff @(posedge clka or posedge rst) begin
    if (rst) begin
      for (i = 0; i <= 256; i++) written[i] <= 1'b0;
    end else if (ena && regcea && wea && in_range_addr(addra)) begin
      shadow_mem[addra] <= dina;
      written   [addra] <= 1'b1;
    end
  end

  // protocol/legal-use checks
  assert property ( (wea) |-> (ena && regcea) )
    else $error("wea asserted without ena&&regcea");

  assert property ( (ena && regcea) |-> in_range_addr(addra) )
    else $error("Access with out-of-range or X addra");

  assert property ( (wea) |-> in_range_addr(addra) )
    else $error("Write with out-of-range or X addra");

  assert property ( !$isunknown({ena,regcea,wea,rst}) )
    else $error("X/Z on control inputs");

  // functional checks
  // When disabled, output must be zero and known
  assert property ( !(ena && regcea) |-> (douta == 12'h000 && !$isunknown(douta)) )
    else $error("douta not 0 when disabled");

  // Valid in-range read returns shadowed data (after first write) and is known
  assert property ( (ena && regcea && in_range_addr(addra) && written[addra])
                    |-> (douta == shadow_mem[addra] && !$isunknown(douta)) )
    else $error("Read data mismatch or X");

  // Same-cycle write-through behavior when reading and writing same address
  assert property ( (ena && regcea && wea && in_range_addr(addra))
                    |-> (douta == dina) )
    else $error("Write-through mismatch on same-cycle write/read");

  // No known output Xs when deterministically driven
  assert property ( ( (ena && regcea && in_range_addr(addra) && written[addra]) ||
                      !(ena && regcea) )
                    |-> !$isunknown(douta) )
    else $error("Unexpected X on douta");

  // Coverages
  //  - basic write/read
  cover property ( ena && regcea && wea && in_range_addr(addra) );
  cover property ( ena && regcea && !wea && in_range_addr(addra) && written[addra] );

  //  - same-cycle write-through
  cover property ( ena && regcea && wea && in_range_addr(addra) && douta == dina );

  //  - min/max address accesses
  cover property ( ena && regcea && wea && addra == 16'd0   );
  cover property ( ena && regcea && wea && addra == 16'd256 );

  //  - disabled read drives zero
  cover property ( !(ena && regcea) && douta == 12'h000 );

endmodule

// Bind into the DUT
bind my_memory my_memory_sva u_my_memory_sva (.*);