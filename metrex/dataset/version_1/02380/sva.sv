// SVA for tfr_mem
// Bind inside DUT to access internals like addr_io

module tfr_mem_sva;

  // helper
  function automatic [31:0] bitmask32(input [4:0] idx);
    bitmask32 = 32'h1 << idx;
  endfunction

  // No simultaneous read and write on bus side
  assert property (@(posedge busclk_i) disable iff (!nreset_i)
    !(~nRD_i && ~nWR_i))
  else $error("tfr_mem: nRD_i and nWR_i low simultaneously");

  // Reset values
  assert property (@(posedge busclk_i)
    !nreset_i |=> (addr_io==24'd0 && bus_D_o==8'd0 && romflags_o==32'd0));

  // Read mapping (lookup_register)
  assert property (@(posedge busclk_i) disable iff (!nreset_i)
    (!nRD_i) |=> (
      (A_i==4'h0 && D_o==$past(addr_io[7:0]))   ||
      (A_i==4'h1 && D_o==$past(addr_io[15:8]))  ||
      (A_i==4'h2 && D_o==$past(addr_io[23:16])) ||
      (A_i==4'h4 && D_o==$past(romflags_o[7:0]))   ||
      (A_i==4'h5 && D_o==$past(romflags_o[15:8]))  ||
      (A_i==4'h6 && D_o==$past(romflags_o[23:16])) ||
      (A_i==4'h7 && D_o==$past(romflags_o[31:24])) ||
      (!(A_i inside {4'h0,4'h1,4'h2,4'h4,4'h5,4'h6,4'h7}) && D_o==8'hFF)
    ));

  // Writes to addr_io byte lanes
  assert property (@(posedge busclk_i) disable iff (!nreset_i)
    (!nWR_i && (A_i inside {4'h0,4'h1,4'h2})) |=> (
      (A_i==4'h0 && addr_io[7:0]==$past(D_i)    && addr_io[23:8]==$past(addr_io[23:8])) ||
      (A_i==4'h1 && addr_io[15:8]==$past(D_i)   && {addr_io[23:16],addr_io[7:0]}==$past({addr_io[23:16],addr_io[7:0]})) ||
      (A_i==4'h2 && addr_io[23:16]==$past(D_i)  && addr_io[15:0]==$past(addr_io[15:0]))
    ));

  // Write to romflags: indexed bit only
  let idx = $past(D_i[4:0]);
  let msk = bitmask32(idx);
  assert property (@(posedge busclk_i) disable iff (!nreset_i)
    (!nWR_i && A_i==4'h4) |=> (
      romflags_o[idx] == $past(D_i[7]) &&
      (romflags_o & ~msk) == ($past(romflags_o) & ~msk)
    ));

  // Write to 0xF: update bus_D_o and auto-increment addr_io
  assert property (@(posedge busclk_i) disable iff (!nreset_i)
    (!nWR_i && A_i==4'hF) |=> (bus_D_o==$past(D_i) && addr_io==$past(addr_io)+24'd1));

  // Writes to unsupported addresses do not modify state
  assert property (@(posedge busclk_i) disable iff (!nreset_i)
    (!nWR_i && (A_i inside {4'h3,4'h5,4'h6,4'h7,4'h8,4'h9,4'hA,4'hB,4'hC,4'hD,4'hE})) |=> 
      ($stable(addr_io) && $stable(romflags_o) && $stable(bus_D_o)));

  // memclk: bus_A_o reflects addr_io - 1 from previous memclk sample
  assert property (@(posedge memclk_i)
    bus_A_o == $past(addr_io) - 24'd1);

  // Coverage

  // Reset coverage
  cover property (@(posedge busclk_i) !nreset_i ##1 (addr_io==24'd0 && bus_D_o==8'd0 && romflags_o==32'd0));

  // Write coverage
  cover property (@(posedge busclk_i) !nWR_i && A_i==4'h0);
  cover property (@(posedge busclk_i) !nWR_i && A_i==4'h1);
  cover property (@(posedge busclk_i) !nWR_i && A_i==4'h2);
  cover property (@(posedge busclk_i) !nWR_i && A_i==4'h4);
  cover property (@(posedge busclk_i) !nWR_i && A_i==4'hF);

  // Read coverage
  cover property (@(posedge busclk_i) !nRD_i && A_i==4'h0);
  cover property (@(posedge busclk_i) !nRD_i && A_i==4'h1);
  cover property (@(posedge busclk_i) !nRD_i && A_i==4'h2);
  cover property (@(posedge busclk_i) !nRD_i && A_i==4'h4);
  cover property (@(posedge busclk_i) !nRD_i && A_i==4'h5);
  cover property (@(posedge busclk_i) !nRD_i && A_i==4'h6);
  cover property (@(posedge busclk_i) !nRD_i && A_i==4'h7);
  cover property (@(posedge busclk_i) !nRD_i && !(A_i inside {4'h0,4'h1,4'h2,4'h4,4'h5,4'h6,4'h7}));

  // romflags bit index extremes
  cover property (@(posedge busclk_i) !nWR_i && A_i==4'h4 && D_i[4:0]==5'd0);
  cover property (@(posedge busclk_i) !nWR_i && A_i==4'h4 && D_i[4:0]==5'd31);

  // addr_io wrap by A==0xF write
  cover property (@(posedge busclk_i) $past(addr_io)==24'hFFFFFF && !nWR_i && A_i==4'hF ##1 addr_io==24'd0);

  // bus_A_o underflow (addr_io==0 => bus_A_o==0xFFFFFF at memclk)
  cover property (@(posedge memclk_i) $past(addr_io)==24'd0 && bus_A_o==24'hFFFFFF);

endmodule

bind tfr_mem tfr_mem_sva tfr_mem_sva_inst();