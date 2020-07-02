`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 06/27/2020 02:40:52 PM
// Design Name: 
// Module Name: mips
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////

//ALU
//000 F = A & B
//001 F = A | B
//010 F = A + B
//100 F = A & (~B)
//101 F = A | (~B)
//110 F = A - B
//111 F = A < B
module alu(
    input logic [31:0] alu_a, alu_b,
    input logic [2:0]   alu_control,
    output logic [31:0] alu_y,
    output logic zero
    );
    
    always_comb begin
        case(alu_control)
            3'b000:      alu_y = alu_a & alu_b;
            3'b001:       alu_y = alu_a | alu_b;
            3'b010:     alu_y = alu_a + alu_b;
            3'b100:  alu_y = alu_a &~alu_b;
            3'b101: alu_y = (alu_a - alu_b == 0 )? 1 : 0;
            3'b110:    alu_y = alu_a - alu_b;
            3'b111:      alu_y = alu_a < alu_b;
            3'b011:   alu_y = 0;
        endcase
    end
    assign zero = alu_y == 0 ? 1 : 0;
endmodule

//2-way multiplexer
//y = s ? d0 : d1
module mux2 #(parameter WIDTH = 8)(
    input logic [WIDTH-1:0] dO, dl,
    input logic s,
    output logic [WIDTH-1:0] y);
    
    assign y = s ? dl : dO;
endmodule

module mux4 #(parameter WIDTH = 8)(
    input logic [WIDTH-1:0] d0, d1, d2, d3,
    input logic [1:0] s,
    output logic [WIDTH-1:0] y);
    
    assign y = (s==2'b00) ? d0 : ( (s==2'b01) ? d1 : ( (s==2'b10) ? d2 : d3 ) );
    
endmodule

//register
//on the posedge of clk
//q <= d
//output q
//reset q to when reset is set as true
module flopr #(parameter WIDTH = 8)(
    input logic clk, reset,
    input logic [WIDTH-1:0] d,
    output logic [WIDTH-1:0] q);
    
    always_ff @(posedge clk, posedge reset) begin
        if (reset) q <= 0;
        else q <= d;
    end
endmodule

module flopenr #(parameter WIDTH=8)(
    input logic clk, reset, en,
    input logic [WIDTH-1:0] d,
    output logic [WIDTH-1:0] q
    );
    
    always_ff @(posedge clk, posedge reset) begin
        if (reset) q <= 0;
        else if (en) q <= d;
    end
endmodule

//signed extension
// y = (int_32) a
module signext(
    input logic [15:0] a,
    output logic [31:0] y);
    
    assign y = {{16{a[15]}}, a};
endmodule

//shift left by 2
//y = a << 2
module sl2(
    input logic [31:0] a,
    output logic [31:0] y);
// shift left by 2
    assign y = {a[29:0], 2'b00};
endmodule

//adder
//y = a + b
module adder(
    input logic [31:0] a, b,
    output logic [31:0] y);
    assign y = a+b;
endmodule

//register file
//32 32-bit registers
//two read ports ra1, ra2
//one write port wa3
//write to register if we3 set as true
module regfile(
    input logic clk,
    input logic we3,
    input logic [4:0] ra1,ra2,wa3,
    input logic [31:0] wd3,
    output logic [31:0] rd1, rd2,
    output logic [31:0] regs [31:0]//added to shoot troubles
    );

    logic [31:0] rf[31:0];
// three ported register file
// read two ports combi nationally
// write third port on rising edge of clk
// register 0 hardwired to 0
// note: for pipelined processor, write third port
// on falling edge of clk
    assign regs = rf;
    always_ff @(posedge clk) begin
        if (we3) rf[wa3] <=wd3;
        assign rd1 = (ra1!=0) ? rf[ra1] : 0;
        assign rd2 = (ra2!=0) ? rf[ra2] : 0;
        //$display("wa3:%H, wd3:%H, ra1:%H, rd1:%H, ra2:%H, rd:%H", wa3, wd3, ra1, rf[ra1], ra2, rf[ra2]);
    end
endmodule

//The select signals are MemtoReg, RegDst, IorD, PCSrc, ALUSrcB, and ALUSrcA.
//The enable signals are IRWrite, MemWrite, PCWrite, Branch, and RegWrite.
module datapath(
    input logic CLK, reset, MemtoReg, RegDst, IorD, ALUSrcA,
    input logic [2:0] ALUControl,
    input logic [1:0] ALUSrcB, PCSrc,
    input logic IRWrite,  PCWrite, Branch, RegWrite,
    output logic [5:0] Op, Funct,
    input logic [31:0] RD,
    output logic [31:0] Adr, B,
    output logic [31:0] regs [31:0]
    );

    logic PCEn, Zero;
    logic [4:0] A3, writereg;
    logic [31:0] PC_, PC, ALUOut, Instr, Data, RD1, RD2, SignImm, SignImmSh, SrcA, SrcB, A, WD3, ALUResult, PCJump;

    always_ff@(posedge CLK) begin
        $display("PC:%H, Instr:%H, PCNext:%H, SrcA:%H, SrcB:%H, ALUControl:%H, ALUResult:%H, ALUOut:%H", PC, Instr, PC_, SrcA, SrcB, ALUControl, ALUResult, ALUOut);
    end

    // next PC 1ogic
    //PC
    //instruction address, converted to @instr
    assign PCEn = PCWrite | (Branch & Zero);
    
    flopenr#(32) pcreg(CLK, reset, PCEn, PC_, PC);
    
    mux2#(32) addr(PC, ALUOut, IorD, Adr);
    
    flopenr#(32) instrReg(CLK, reset, IRWrite, RD, Instr);
    
    assign Op = Instr[31:26];
    assign Funct = Instr[5:0];
    
    mux2#(5) a3Mux(Instr[20:16], Instr[15:11], RegDst, A3);
    
    flopr#(32) datareg(CLK, reset, RD, Data);
    
    mux2#(32) wd3Mux(ALUOut, Data, MemtoReg, WD3);
    
    regfile rf(CLK, RegWrite, Instr[25:21], Instr[20:16], A3, WD3, RD1, RD2, regs);
    
    flopr#(32) a(CLK, reset, RD1, A);
    flopr#(32) b(CLK, reset, RD2, B);
    
    signext se(Instr[15:0], SignImm);
    
    sl2 immsh(SignImm, SignImmSh) ;
    
    mux2#(32) srcAMux2(PC, A, ALUSrcA, SrcA);
    
    mux4#(32) srcBMux4(B, 32'b100, SignImm, SignImmSh, ALUSrcB, SrcB);
    
    alu alu(SrcA, SrcB, ALUControl, ALUResult, Zero);
    
    flopr#(32) aluout(CLK, reset, ALUResult, ALUOut);
    
    assign PCJump[31:28] = PC[31:28];
    
    sl2 pcjumpsh(Instr[25:0], PCJump[27:0]);
    
    mux4#(32) mux2pc(ALUResult, ALUOut, PCJump, 0, PCSrc, PC_);

endmodule


//decide the alu control bit given the funct field and aluop field of the instruction
//combinational logic
module aludec(
    input logic [5:0] funct,
    input logic [1:0] aluop,
    output logic [2:0] alucontrol);
    
    always_comb
        case(aluop)
            2'b00: alucontrol <= 3'b010; // add (for lw/sw/addi) end;
            2'b01: alucontrol <= 3'b110; // sub (for beq) architecture behave of aludec is
            default: case(funct) // R-type instructions begin
                6'b100000: alucontrol <= 3'b010; // add process(al1 ) begin
                6'b100010: alucontrol <= 3'b110; // sub case aluop is
                6'b100100: alucontrol <= 3'b000; // and when "00" => alucontrol <= "010" ; -- add (for lw/sw/addi )
                6'b100101: alucontrol <= 3'b001; //or when "01" => alucontrol <= "110"; -- sub (for beq)
                6'b101010: alucontrol <= 3'b111; // sit when others => case funct is - R-type instructions
                default: alucontrol <= 3'bxxx; // ??? when "100000" => alucontrol <= "010"; - add
            endcase // when "100010" => alucontrol <= "110"; - sub
        endcase // when "100100" => alucontrol <= "000"; -- and
endmodule

module maindec(
    input logic CLK, reset,
    input logic [5:0] Op,
    output logic [1:0] ALUOp,
    output logic MemtoReg, RegDst, IorD,
    output logic [1:0] PCSrc,
    output logic ALUSrcA,
    output logic [1:0] ALUSrcB,
    output logic IRWrite, MemWrite, PCWrite, Branch, RegWrite
    );
    
    logic [3:0] nextState, S, counter;
    logic [14:0] controlbits;
    
    assign MemtoReg = controlbits[14];
    assign RegDst = controlbits[13];
    assign IorD = controlbits[12];
    assign ALUSrcA = controlbits[11];
    assign PCSrc = controlbits[10:9];
    assign ALUSrcB = controlbits[8:7];
    assign ALUOp = controlbits[6:5];
    assign {IRWrite, MemWrite, PCWrite, Branch, RegWrite} = controlbits[4:0];
    
    always_comb begin
        case(S)
            0: controlbits = 15'b0000_00_01_00_10100;
            1: controlbits = 15'b0000_00_11_00_00000;
            2: controlbits = 15'b0001_00_10_00_00000;
            3: controlbits = 15'b0010_00_00_00_00000;
            4: controlbits = 15'b1000_00_00_00_00001;
            5: controlbits = 15'b0010_00_00_00_01000;
            6: controlbits = 15'b0001_00_00_10_00000;
            7: controlbits = 15'b0100_00_00_00_00001;
            
            8: controlbits = 15'b0001_01_00_01_00010;
            9: controlbits = 15'b0001_00_10_00_00000;
            10: controlbits = 15'b0000_00_00_00_00001;
            11: controlbits = 15'b0000_10_00_00_00100;
        endcase
    end
    
    always_comb begin
        case(S)
            0: nextState = 1;
            1: case(Op)
                6'b100011: nextState = 2;
                6'b101011: nextState = 2;
                6'b000000: nextState = 6;
                6'b000100: nextState = 8;
                6'b001000: nextState = 9;
                6'b000010: nextState = 11;
            endcase
            2: case(Op)
                6'b100011: nextState = 3;
                6'b101011: nextState = 5;
            endcase
            3: nextState = 4;
            4: nextState = 0;
            5: nextState = 0;
            6: nextState = 7;
            7: nextState = 0;
            8: nextState = 0;
            9: nextState = 10;
            10: nextState = 0;
            11: nextState = 0;
        endcase
    end
    
    always_ff @(posedge CLK, posedge reset) begin
        if(reset) begin
            S <= 0;
            counter <= 0;
        end
        else begin
            S <= nextState;//S == 0 ? 1: (S == 1 ? (Op == 6'b100011 | Op == 6'b101011 ? 2 : (Op==6'b000000 ? 6 : (Op==6'b000100 ? 8 : 9))):(S == 2 ? (Op==6'b100011 ? 3 : 5) : (S == 3 ? 4 : (S == 4 | S == 5 | S == 7 | S == 8 | S == 10? 0 : ( S == 6 ? 7 : 10)))));
            counter <= counter + 1;
        end
         $display("counter:%H, S:%H, controlbits:%H, op:%H, MemtoReg:%H, RegDst:%H, IorD:%H, ALUSrcA:%H, PCSrc:%H, ALUSrcB:%H, ALUOp:%H, IRWrite:%H, MemWrite:%H, PCWrite:%H, Branch:%H, RegWrite:%H", counter, S, controlbits, Op, MemtoReg, RegDst, IorD, ALUSrcA, PCSrc, ALUSrcB, ALUOp, IRWrite, MemWrite, PCWrite, Branch, RegWrite);
    end
    
endmodule


module controller(
    input logic CLK, reset,
    input logic [5:0] Op, Funct,
    output logic MemtoReg, RegDst, IorD,
    output logic [1:0] PCSrc,
    output logic ALUSrcA,
    output logic [2:0] ALUControl,
    output logic [1:0] ALUSrcB,
    output logic IRWrite, MemWrite, PCWrite, Branch, RegWrite
    );
    
    logic [11:0] controlbits;
    logic [1:0] ALUOp;
    
    aludec ad(Funct, ALUOp, ALUControl);
    
    maindec md(CLK, reset, Op, ALUOp, MemtoReg, RegDst, IorD, PCSrc, ALUSrcA, ALUSrcB, IRWrite, MemWrite, PCWrite, Branch, RegWrite);
    /*
    always_ff@(posedge CLK) begin
        $display("ALUOp:%H, ALUControl:%H, ALUSrcB:%H", ALUOp, ALUControl, ALUSrcB);
    end
    */
endmodule


module mips(
    input logic clk, reset,
    output logic [31:0] Adr, writedata,
    output logic MemWrite,
    input logic [31:0] readdata,
    output logic [31:0] regs [31:0]
    );
    
    logic MemtoReg, RegDst, IorD, ALUSrcA;
    logic [2:0] ALUControl;
    logic [1:0] ALUSrcB, PCSrc;
    logic IRWrite, PCWrite, Branch, RegWrite;
    logic Zero;
    logic [5:0] Op, Funct;

    datapath dp(clk, reset, MemtoReg, RegDst, IorD, ALUSrcA, ALUControl, ALUSrcB, PCSrc, IRWrite, PCWrite, Branch, RegWrite, Op, Funct, readdata, Adr, writedata, regs);
    
    controller ctlr(clk, reset, Op, Funct, MemtoReg, RegDst, IorD, PCSrc, ALUSrcA, ALUControl, ALUSrcB, IRWrite, MemWrite, PCWrite, Branch, RegWrite);
   
endmodule


module top(
    input logic clk, reset,
    output logic [31:0] writedata, adr,
    output logic memwrite,
    output logic [31:0] regs [31:0]
    );
    
    logic [31:0] readdata;
    
    // instantiate processor and memories
    mips mips(clk, reset, adr , writedata , memwrite , readdata, regs);
    mem mem(clk, memwrite, adr, writedata, readdata);

endmodule


module mem(
    input logic clk, we,
    input logic [31:0] a, wd,
    output logic [31:0] rd
    );
    
    logic [31:0] RAM[63:0] ;

    initial begin
        RAM[0] = 32'h20020005;
        RAM[1] = 32'h2003000c;
//        RAM[0] = 32'h34020005;
//        RAM[1] = 32'h3403000c;
        RAM[2] = 32'h2067fff7;
        RAM[3] = 32'h00e22025;
        RAM[4] = 32'h00642824;
        RAM[5] = 32'h00a42820;
        RAM[6] = 32'h10a7000a;
        RAM[7] = 32'h0064202a;
        RAM[8] = 32'h10800001;
        RAM[9] = 32'h20050000;
        RAM[10] = 32'h00e2202a;
        RAM[11] = 32'h00853820;
        RAM[12] = 32'h00e23822;
        RAM[13] = 32'hac670044;
        RAM[14] = 32'h8c020050;
        RAM[15] = 32'h08000011;
        RAM[16] = 32'h20020001;
        RAM[17] = 32'hac020054;
    end
    
    assign rd = RAM[a[31:2]]; // word aligned

    always @(posedge clk)
        if (we)
            RAM[a[31:2]] <= wd;

endmodule

//test
module testbench();

    logic clk;
    logic reset;
    
    logic [31:0] writedata, dataadr;
    logic memwrite;
    logic [31:0] regs [31:0];

    // instantiate device to be tested
    top dut(clk, reset, writedata, dataadr, memwrite, regs);

    // initialize test end component;
    // set PC as 0
    // start the CPU
    initial
        begin
            $display("Simulation started");
            reset <= 1; # 22; reset <= 0;
        end

    // time period = 10
    always
        begin
            clk <=1; # 5; clk <=0; #5;
        end


    // check results
    always @(negedge clk)
        begin
            if (memwrite)
                begin
                    if (dataadr === 84 & writedata === 7)
                        begin
                            $display("Simulation succeeded");
                            $stop;
                        end
                    
                    else if (dataadr !== 80)
                        begin
                            $display("Simulation failed");
                            $stop;
                        end
                end
        end
endmodule
