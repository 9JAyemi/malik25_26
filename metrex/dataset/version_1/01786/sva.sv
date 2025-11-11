// SVA for softusb_hostif
// Bind this module to the DUT
module softusb_hostif_sva #(parameter csr_addr = 4'h0, parameter pmem_width = 12) ();

  // --------- Helpers ---------
  wire        sys_clk;
  wire        sys_rst;
  wire        usb_clk;

  wire [13:0] csr_a;
  wire        csr_we;
  wire [31:0] csr_di;
  wire [31:0] csr_do;

  wire        usb_rst;
  wire        irq;

  wire [pmem_width-1:0] dbg_pc;

  // Internal DUT regs (hierarchical in bound scope)
  wire usb_rst0 = usb_rst0;
  wire usb_rst1 = usb_rst1;

  wire irq_flip  = irq_flip;
  wire irq_flip0 = irq_flip0;
  wire irq_flip1 = irq_flip1;
  wire irq_flip2 = irq_flip2;

  wire addr_match = (csr_a[13:10] == csr_addr);

  // --------- CSR interface (sys_clk) ---------

  // Reset effects
  assert property (@(posedge sys_clk) sys_rst |-> (usb_rst0 == 1'b1 && csr_do == 32'h0));

  // csr_do contents when addressed
  assert property (@(posedge sys_clk)
    !sys_rst && addr_match |-> (csr_do[0] == 1'b0
                                && csr_do[pmem_width:1] == dbg_pc
                                && csr_do[31:pmem_width+1] == '0));

  // csr_do is zero when not addressed
  assert property (@(posedge sys_clk) !sys_rst && !addr_match |-> (csr_do == 32'h0));

  // Writes: update usb_rst0 only on address match
  assert property (@(posedge sys_clk)
    !sys_rst && csr_we && addr_match |=> (usb_rst0 == $past(csr_di[0])));

  assert property (@(posedge sys_clk)
    !sys_rst && csr_we && !addr_match |=> $stable(usb_rst0));

  // --------- usb_rst synchronizer (usb_clk) ---------

  // Two-stage sync: usb_rst0 -> usb_rst1 -> usb_rst
  assert property (@(posedge usb_clk) usb_rst1 == $past(usb_rst0));
  assert property (@(posedge usb_clk) usb_rst  == $past(usb_rst1));

  // --------- IRQ generation in usb_clk domain ---------

  // Reset forces irq_flip low
  assert property (@(posedge usb_clk) usb_rst |-> (irq_flip == 1'b0));

  // Toggle only on io write to 0x15 when not in reset
  assert property (@(posedge usb_clk)
    !usb_rst && io_we && (io_a == 6'h15) |=> (irq_flip == !$past(irq_flip)));

  // Otherwise hold value
  assert property (@(posedge usb_clk)
    !usb_rst && !(io_we && (io_a == 6'h15)) |=> $stable(irq_flip));

  // --------- IRQ synchronizer and pulse (sys_clk) ---------

  // Three-stage sync from usb to sys
  assert property (@(posedge sys_clk) irq_flip0 == $past(irq_flip));
  assert property (@(posedge sys_clk) irq_flip1 == $past(irq_flip0));
  assert property (@(posedge sys_clk) irq_flip2 == $past(irq_flip1));

  // irq is exactly the XOR of the last two stages and is one-cycle wide
  assert property (@(posedge sys_clk) irq == (irq_flip1 ^ irq_flip2));
  assert property (@(posedge sys_clk) irq |=> !irq);

  // irq iff a toggle is observed at irq_flip1
  assert property (@(posedge sys_clk) (irq_flip1 != $past(irq_flip1)) |-> irq);
  assert property (@(posedge sys_clk) irq |-> (irq_flip1 != $past(irq_flip1)));

  // --------- Coverage ---------

  // Exercise CSR read path when addressed
  cover property (@(posedge sys_clk) !sys_rst ##1 addr_match);

  // Exercise usb_rst programming 0->1
  cover property (@(posedge sys_clk)
    !sys_rst ##1 (csr_we && addr_match && (csr_di[0] == 1'b0))
    ##1 (csr_we && addr_match && (csr_di[0] == 1'b1)));

  // Exercise IRQ toggle and observe sys_clk irq pulse
  cover property (@(posedge usb_clk) !usb_rst ##1 (io_we && io_a == 6'h15));
  cover property (@(posedge sys_clk) $rose(irq));

endmodule

bind softusb_hostif softusb_hostif_sva #(.csr_addr(csr_addr), .pmem_width(pmem_width)) softusb_hostif_sva_b();