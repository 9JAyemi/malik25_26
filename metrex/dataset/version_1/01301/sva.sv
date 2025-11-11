// SVA for anteconmutador
// Binds into DUT and checks core behavior, invariants, and key coverage

module anteconmutador_sva (anteconmutador dut);
  default clocking cb @(posedge dut.clk); endclocking

  // Start-of-conversion book-keeping
  logic [7:0] start_count;
  logic       in_run;
  wire        start_evt = dut.calculate && !$past(dut.calculate);

  always_ff @(posedge dut.clk) begin
    if (!dut.calculate) begin
      in_run <= 1'b0;
    end else if (start_evt) begin
      in_run     <= 1'b1;
      start_count <= dut.count;
    end
  end

  // Small helpers
  function automatic [3:0] f_h (input [7:0] x); f_h = x/8'd100; endfunction
  function automatic [3:0] f_t (input [7:0] x); f_t = (x%8'd100)/8'd10; endfunction
  function automatic [3:0] f_u (input [7:0] x); f_u = x%8'd10; endfunction

  // Reset path (calculate=0) forces clear state
  assert property ( !dut.calculate |-> dut.centenas==0 && dut.decenas==0 && dut.unidades==0 &&
                                     dut.C==0 && dut.De==0 && dut.U==0 &&
                                     dut.i==1 && dut.digitT==0 );

  // Latch-on-start
  assert property ( start_evt |-> dut.i==0 && dut.digitT==dut.count );

  // Ranges always respected
  assert property ( dut.centenas<=4'd2 && dut.decenas<=4'd9 && dut.unidades<=4'd9 );

  // Conservation invariant during run: start_count == 100*C + 10*D + digitT
  assert property ( in_run |-> start_count == (dut.centenas*8'd100 + dut.decenas*8'd10 + dut.digitT) );

  // Step behavior: hundreds subtraction
  assert property ( dut.calculate && $past(dut.calculate) && $past(dut.digitT)>8'd99 |->
                    dut.digitT==$past(dut.digitT)-8'd100 &&
                    dut.centenas==$past(dut.centenas)+1 &&
                    dut.decenas==$past(dut.decenas) &&
                    dut.unidades==$past(dut.unidades) &&
                    dut.C==$past(dut.C) && dut.De==$past(dut.De) && dut.U==$past(dut.U) );

  // Step behavior: tens subtraction
  assert property ( dut.calculate && $past(dut.calculate) &&
                    $past(dut.digitT)<=8'd99 && $past(dut.digitT)>8'd9 |->
                    dut.digitT==$past(dut.digitT)-8'd10 &&
                    dut.decenas==$past(dut.decenas)+1 &&
                    dut.centenas==$past(dut.centenas) &&
                    dut.unidades==$past(dut.unidades) &&
                    dut.C==$past(dut.C) && dut.De==$past(dut.De) && dut.U==$past(dut.U) );

  // Finalize step and flags
  assert property ( dut.calculate && $past(dut.calculate) && $past(dut.digitT)<=8'd9 |->
                    dut.unidades==$past(dut.digitT[3:0]) &&
                    dut.centenas==$past(dut.centenas) && dut.decenas==$past(dut.decenas) &&
                    dut.C==(dut.centenas>=1) && dut.De==(dut.decenas>=1) && dut.U==(dut.unidades>=1) );

  // Bounded completion (max 11 cycles for any 8-bit count)
  localparam int MAX_CYCLES = 11;
  assert property ( start_evt |-> ##[1:MAX_CYCLES] (dut.digitT<=8'd9) );

  // Functional correctness at completion
  assert property ( in_run && dut.digitT<=8'd9 |->
                    dut.centenas==f_h(start_count) &&
                    dut.decenas==f_t(start_count) &&
                    dut.unidades==f_u(start_count) &&
                    dut.C==(f_h(start_count)>=1) &&
                    dut.De==(f_t(start_count)>=1) &&
                    dut.U==(f_u(start_count)>=1) );

  // Stability when held in reset mode
  assert property ( !dut.calculate && !$past(dut.calculate) |->
                    $stable(dut.centenas) && $stable(dut.decenas) && $stable(dut.unidades) &&
                    $stable(dut.C) && $stable(dut.De) && $stable(dut.U) &&
                    $stable(dut.i) && $stable(dut.digitT) );

  // Key coverage
  cover property ( start_evt ##[1:$] (dut.digitT>8'd99) );         // hundreds phase seen
  cover property ( start_evt ##[1:$] (dut.digitT<=8'd99 && dut.digitT>8'd9) ); // tens phase
  cover property ( start_evt ##[1:$] (dut.digitT<=8'd9) );         // finalize reached
  cover property ( start_evt && start_count==8'd0  ##[1:$] (dut.digitT<=8'd9) );
  cover property ( start_evt && start_count==8'd9  ##[1:$] (dut.digitT<=8'd9) );
  cover property ( start_evt && start_count==8'd10 ##[1:$] (dut.digitT<=8'd9) );
  cover property ( start_evt && start_count==8'd99 ##[1:$] (dut.digitT<=8'd9) );
  cover property ( start_evt && start_count==8'd100##[1:$] (dut.digitT<=8'd9) );
  cover property ( start_evt && start_count==8'd199##[1:$] (dut.digitT<=8'd9) );
  cover property ( start_evt && start_count==8'd200##[1:$] (dut.digitT<=8'd9) );
  cover property ( start_evt && start_count==8'd255##[1:$] (dut.digitT<=8'd9) );
  cover property ( in_run && dut.digitT<=8'd9 && dut.C );
  cover property ( in_run && dut.digitT<=8'd9 && dut.De );
  cover property ( in_run && dut.digitT<=8'd9 && dut.U );
endmodule

bind anteconmutador anteconmutador_sva sva_anteconmutador();