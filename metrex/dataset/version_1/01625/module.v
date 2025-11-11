module vga_controller(
    input vclock,
    output reg [10:0] hcount,
    output reg [9:0] vcount,
    output reg vsync,
    output reg hsync,
    output reg blank
);

    // horizontal: 1056 pixels total
    // display 800 pixels per line
    reg hblank;
    wire hblankon, hsyncon, hsyncoff, hreset;
    assign hblankon = (hcount == 799);
    assign hsyncon = (hcount == 839);
    assign hsyncoff = (hcount == 967);
    assign hreset = (hcount == 1055);

    // vertical: 628 lines total
    // display 600 lines
    reg vblank;
    wire vblankon, vsyncon, vsyncoff, vreset;
    assign vblankon = hreset & (vcount == 599);
    assign vsyncon = hreset & (vcount == 600);
    assign vsyncoff = hreset & (vcount == 604);
    assign vreset = hreset & (vcount == 627);

    // sync and blanking
    wire next_hblank, next_vblank;
    assign next_hblank = hreset ? 0 : hblankon ? 1 : hblank;
    assign next_vblank = vreset ? 0 : vblankon ? 1 : vblank;
    always @(posedge vclock) begin
        hcount <= hreset ? 0 : hcount + 1;
        hblank <= next_hblank;
        hsync <= hsyncon ? 0 : hsyncoff ? 1 : hsync;  // active low

        vcount <= hreset ? (vreset ? 0 : vcount + 1) : vcount;
        vblank <= next_vblank;
        vsync <= vsyncon ? 0 : vsyncoff ? 1 : vsync;  // active low

        blank <= next_vblank | (next_hblank & ~hreset);
    end
endmodule