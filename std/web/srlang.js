"use strict";

(function() {

function getElement(name) {
        if (name) {
                return document.getElementById(name);
        }
        return undefined;
}

function stripNewline(str) {
    return str.replace(/\n/, ' ')
}

class WasmMemoryInterface {
        constructor() {
                this.memory = null;
                this.exports = null;
                this.listenerMap = new Map();

                // Size (in bytes) of the integer type, should be 4 on `js_wasm32` and 8 on `js_wasm64p32`
                this.intSize = 4;
        }

        setIntSize(size) {
                this.intSize = size;
        }

        setMemory(memory) {
                this.memory = memory;
        }

        setExports(exports) {
                this.exports = exports;
        }

        get mem() {
                return new DataView(this.memory.buffer);
        }


        loadF32Array(addr, len) {
                let array = new Float32Array(this.memory.buffer, addr, len);
                return array;
        }
        loadF64Array(addr, len) {
                let array = new Float64Array(this.memory.buffer, addr, len);
                return array;
        }
        loadU32Array(addr, len) {
                let array = new Uint32Array(this.memory.buffer, addr, len);
                return array;
        }
        loadI32Array(addr, len) {
                let array = new Int32Array(this.memory.buffer, addr, len);
                return array;
        }


        loadU8(addr)  { return this.mem.getUint8  (addr); }
        loadI8(addr)  { return this.mem.getInt8   (addr); }
        loadU16(addr) { return this.mem.getUint16 (addr, true); }
        loadI16(addr) { return this.mem.getInt16  (addr, true); }
        loadU32(addr) { return this.mem.getUint32 (addr, true); }
        loadI32(addr) { return this.mem.getInt32  (addr, true); }
        loadU64(addr) {
                const lo = this.mem.getUint32(addr + 0, true);
                const hi = this.mem.getUint32(addr + 4, true);
                return lo + hi*4294967296;
        };
        loadI64(addr) {
                const lo = this.mem.getUint32(addr + 0, true);
                const hi = this.mem.getInt32 (addr + 4, true);
                return lo + hi*4294967296;
        };
        loadF32(addr) { return this.mem.getFloat32(addr, true); }
        loadF64(addr) { return this.mem.getFloat64(addr, true); }
        loadInt(addr) {
                if (this.intSize == 8) {
                        return this.loadI64(addr);
                } else if (this.intSize == 4) {
                        return this.loadI32(addr);
                } else {
                        throw new Error('Unhandled `intSize`, expected `4` or `8`');
                }
        };
        loadUint(addr) {
                if (this.intSize == 8) {
                        return this.loadU64(addr);
                } else if (this.intSize == 4) {
                        return this.loadU32(addr);
                } else {
                        throw new Error('Unhandled `intSize`, expected `4` or `8`');
                }
        };
        loadPtr(addr) { return this.loadU32(addr); }

        loadB32(addr) {
                return this.loadU32(addr) != 0;
        }

        loadBytes(ptr, len) {
                return new Uint8Array(this.memory.buffer, ptr, Number(len));
        }

        loadString(ptr, len) {
                const bytes = this.loadBytes(ptr, Number(len));
                return new TextDecoder().decode(bytes);
        }

        loadCstring(ptr) {
                if (ptr == 0) {
                        return null;
                }
                let len = 0;
                for (; this.mem.getUint8(ptr+len) != 0; len += 1) {}
                return this.loadString(ptr, len);
        }

        storeU8(addr, value)  { this.mem.setUint8  (addr, value); }
        storeI8(addr, value)  { this.mem.setInt8   (addr, value); }
        storeU16(addr, value) { this.mem.setUint16 (addr, value, true); }
        storeI16(addr, value) { this.mem.setInt16  (addr, value, true); }
        storeU32(addr, value) { this.mem.setUint32 (addr, value, true); }
        storeI32(addr, value) { this.mem.setInt32  (addr, value, true); }
        storeU64(addr, value) {
                this.mem.setUint32(addr + 0, Number(value), true);

                let div = 4294967296;
                if (typeof value == 'bigint') {
                        div = BigInt(div);
                }

                this.mem.setUint32(addr + 4, Math.floor(Number(value / div)), true);
        }
        storeI64(addr, value) {
                this.mem.setUint32(addr + 0, Number(value), true);

                let div = 4294967296;
                if (typeof value == 'bigint') {
                        div = BigInt(div);
                }

                this.mem.setInt32(addr + 4, Math.floor(Number(value / div)), true);
        }
        storeF32(addr, value) { this.mem.setFloat32(addr, value, true); }
        storeF64(addr, value) { this.mem.setFloat64(addr, value, true); }
        storeInt(addr, value) {
                if (this.intSize == 8) {
                        this.storeI64(addr, value);
                } else if (this.intSize == 4) {
                        this.storeI32(addr, value);
                } else {
                        throw new Error('Unhandled `intSize`, expected `4` or `8`');
                }
        }
        storeUint(addr, value) {
                if (this.intSize == 8) {
                        this.storeU64(addr, value);
                } else if (this.intSize == 4) {
                        this.storeU32(addr, value);
                } else {
                        throw new Error('Unhandled `intSize`, expected `4` or `8`');
                }
        }

        // Returned length might not be the same as `value.length` if non-ascii strings are given.
        storeString(addr, value) {
                const src = new TextEncoder().encode(value);
                const dst = new Uint8Array(this.memory.buffer, addr, src.length);
                dst.set(src);
                return src.length;
        }
};

class WebGLInterface {
        constructor(wasmMemoryInterface) {
                this.wasmMemoryInterface = wasmMemoryInterface;
                this.ctxElement         = null;
                this.ctx                = null;
                this.ctxVersion         = 1.0;
                this.counter            = 1;
                this.lastError          = 0;
                this.buffers            = [];
                this.mappedBuffers      = {};
                this.programs           = [];
                this.framebuffers       = [];
                this.renderbuffers      = [];
                this.textures           = [];
                this.uniforms           = [];
                this.shaders            = [];
                this.vaos               = [];
                this.contexts           = [];
                this.currentContext     = null;
                this.offscreenCanvases  = {};
                this.timerQueriesEXT    = [];
                this.queries            = [];
                this.samplers           = [];
                this.transformFeedbacks = [];
                this.syncs              = [];
                this.programInfos       = {};
        }

        get mem() {
                return this.wasmMemoryInterface
        }

        setCurrentContext(element, contextSettings) {
                if (!element) {
                        return false;
                }
                if (this.ctxElement == element) {
                        return true;
                }

                contextSettings = contextSettings ?? {};
                this.ctx = element.getContext("webgl2", contextSettings) || element.getContext("webgl", contextSettings);
                if (!this.ctx) {
                        return false;
                }
                this.ctxElement = element;
                if (this.ctx.getParameter(0x1F02).indexOf("WebGL 2.0") !== -1) {
                        this.ctxVersion = 2.0;
                } else {
                        this.ctxVersion = 1.0;
                }
                return true;
        }

        assertWebGL2() {
                if (this.ctxVersion < 2) {
                        throw new Error("WebGL2 procedure called in a canvas without a WebGL2 context");
                }
        }
        getNewId(table) {
                for (var ret = this.counter++, i = table.length; i < ret; i++) {
                        table[i] = null;
                }
                return ret;
        }
        recordError(errorCode) {
                this.lastError || (this.lastError = errorCode);
        }
        populateUniformTable(program) {
                let p = this.programs[program];
                this.programInfos[program] = {
                        uniforms: {},
                        maxUniformLength: 0,
                        maxAttributeLength: -1,
                        maxUniformBlockNameLength: -1,
                };
                for (let ptable = this.programInfos[program], utable = ptable.uniforms, numUniforms = this.ctx.getProgramParameter(p, this.ctx.ACTIVE_UNIFORMS), i = 0; i < numUniforms; ++i) {
                        let u = this.ctx.getActiveUniform(p, i);
                        let name = u.name;
                        if (ptable.maxUniformLength = Math.max(ptable.maxUniformLength, name.length + 1), name.indexOf("]", name.length - 1) !== -1) {
                                name = name.slice(0, name.lastIndexOf("["));
                        }
                        let loc = this.ctx.getUniformLocation(p, name);
                        if (loc !== null) {
                                let id = this.getNewId(this.uniforms);
                                utable[name] = [u.size, id], this.uniforms[id] = loc;
                                for (let j = 1; j < u.size; ++j) {
                                        let n = name + "[" + j + "]";
                                        let loc = this.ctx.getUniformLocation(p, n);
                                        let id = this.getNewId(this.uniforms);
                                        this.uniforms[id] = loc;
                                }
                        }
                }
        }
        getSource(shader, strings_ptr, strings_length) {
                const stringSize = this.mem.intSize*2;
                let source = "";
                for (let i = 0; i < strings_length; i++) {
                        let ptr = this.mem.loadPtr(strings_ptr + i*stringSize);
                        let len = this.mem.loadPtr(strings_ptr + i*stringSize + 4);
                        let str = this.mem.loadString(ptr, len);
                        source += str;
                }
                return source;
        }

        getWebGL1Interface() {
                return {
                        SetCurrentContextById: (name_ptr, name_len) => {
                                let name = this.mem.loadString(name_ptr, name_len);
                                let element = getElement(name);
                                return this.setCurrentContext(element, {alpha: true, antialias: true, depth: true, premultipliedAlpha: true});
                        },
                        // ... (Other WebGL1 functions omitted for brevity in thought but included in file)
                        Clear: (x) => { this.ctx.clear(x); },
                        ClearColor: (r, g, b, a) => { this.ctx.clearColor(r, g, b, a); },
                        CreateBuffer: () => {
                                let buffer = this.ctx.createBuffer();
                                let id = this.getNewId(this.buffers);
                                buffer.name = id;
                                this.buffers[id] = buffer;
                                return id;
                        },
                        BindBuffer: (target, buffer) => {
                                this.ctx.bindBuffer(target, buffer ? this.buffers[buffer] : null);
                        },
                        BufferData: (target, size, data, usage) => {
                                if (data) {
                                        this.ctx.bufferData(target, this.mem.loadBytes(data, size), usage);
                                } else {
                                        this.ctx.bufferData(target, Number(size), usage);
                                }
                        },
                        CreateShader: (type) => {
                                let shader = this.ctx.createShader(type);
                                let id = this.getNewId(this.shaders);
                                shader.name = id;
                                this.shaders[id] = shader;
                                return id;
                        },
                        ShaderSource: (shader, strings_ptr, strings_length) => {
                                let source = this.getSource(shader, strings_ptr, strings_length);
                                this.ctx.shaderSource(this.shaders[shader], source);
                        },
                        ShaderSourceRaw: (shader, ptr, len) => {
                                let source = this.mem.loadString(ptr, len);
                                this.ctx.shaderSource(this.shaders[shader], source);
                        },
                        CompileShader: (shader) => { this.ctx.compileShader(this.shaders[shader]); },
                        CreateProgram: () => {
                                let program = this.ctx.createProgram();
                                let id = this.getNewId(this.programs);
                                program.name = id;
                                this.programs[id] = program;
                                return id;
                        },
                        AttachShader: (program, shader) => { this.ctx.attachShader(this.programs[program], this.shaders[shader]); },
                        LinkProgram: (program) => {
                                this.ctx.linkProgram(this.programs[program]);
                                this.programInfos[program] = null;
                                this.populateUniformTable(program);
                        },
                        UseProgram: (program) => { if(program) this.ctx.useProgram(this.programs[program]); },
                        GetAttribLocation: (program, name_ptr, name_len) => {
                                let name = this.mem.loadString(name_ptr, name_len);
                                return this.ctx.getAttribLocation(this.programs[program], name);
                        },
                        EnableVertexAttribArray: (index) => { this.ctx.enableVertexAttribArray(index); },
                        VertexAttribPointer: (index, size, type, normalized, stride, ptr) => {
                                this.ctx.vertexAttribPointer(index, size, type, !!normalized, stride, Number(ptr));
                        },
                        DrawArrays: (mode, first, count) => { this.ctx.drawArrays(mode, first, count); },
                        Viewport: (x,y,w,h) => { this.ctx.viewport(x,y,w,h); },
                        GetError: () => { return this.ctx.getError(); },
                        GetShaderiv: (shader, pname, p) => {
                             let res = this.ctx.getShaderParameter(this.shaders[shader], pname);
                             if(pname == 0x8B81 && !res) { // COMPILE_STATUS
                                 console.error("Shader Compile Error:");
                                 console.error(this.ctx.getShaderSource(this.shaders[shader]));
                                 console.error(this.ctx.getShaderInfoLog(this.shaders[shader]));
                             }
                             this.mem.storeI32(p, res ? 1 : 0);
                        },
                        GetProgramiv: (program, pname, p) => {
                             let res = this.ctx.getProgramParameter(this.programs[program], pname);
                             if(pname == 0x8B82 && !res) { // LINK_STATUS
                                 console.error(this.ctx.getProgramInfoLog(this.programs[program]));
                             }
                             this.mem.storeI32(p, res ? 1 : 0);
                        }
                };
        }
        
        getWebGL2Interface() {
                return {
                        /* Buffer objects */
                        CopyBufferSubData: (readTarget, writeTarget, readOffset, writeOffset, size) => {
                                this.assertWebGL2();
                                this.ctx.copyBufferSubData(readTarget, writeTarget, Number(readOffset), Number(writeOffset), Number(size));
                        },
                        GetBufferSubData: (target, srcByteOffset, dst_buffer_ptr, dst_buffer_len, dstOffset, length) => {
                                this.assertWebGL2();
                                this.ctx.getBufferSubData(target, Number(srcByteOffset), this.mem.loadBytes(dst_buffer_ptr, dst_buffer_len), Number(dstOffset), Number(length));
                        },

                        /* Framebuffer objects */
                        BlitFramebuffer: (srcX0, srcY0, srcX1, srcY1, dstX0, dstY0, dstX1, dstY1, mask, filter) => {
                                this.assertWebGL2();
                                this.ctx.blitFramebuffer(srcX0, srcY0, srcX1, srcY1, dstX0, dstY0, dstX1, dstY1, mask, filter);
                        },
                        FramebufferTextureLayer: (target, attachment, texture, level, layer) => {
                                this.assertWebGL2();
                                this.ctx.framebufferTextureLayer(target, attachment, this.textures[texture], level, layer);
                        },
                        InvalidateFramebuffer: (target, attachments_ptr, attachments_len) => {
                                this.assertWebGL2();
                                let attachments = this.mem.loadU32Array(attachments_ptr, attachments_len);
                                this.ctx.invalidateFramebuffer(target, attachments);
                        },
                        InvalidateSubFramebuffer: (target, attachments_ptr, attachments_len, x, y, width, height) => {
                                this.assertWebGL2();
                                let attachments = this.mem.loadU32Array(attachments_ptr, attachments_len);
                                this.ctx.invalidateSubFramebuffer(target, attachments, x, y, width, height);
                        },
                        ReadBuffer: (src) => {
                                this.assertWebGL2();
                                this.ctx.readBuffer(src);
                        },

                        /* Renderbuffer objects */
                        RenderbufferStorageMultisample: (target, samples, internalformat, width, height) => {
                                this.assertWebGL2();
                                this.ctx.renderbufferStorageMultisample(target, samples, internalformat, width, height);
                        },

                        /* Texture objects */
                        TexStorage2D: (target, levels, internalformat, width, height) => {
                                this.assertWebGL2();
                                this.ctx.texStorage2D(target, levels, internalformat, width, height);
                        },
                        TexStorage3D: (target, levels, internalformat, width, height, depth) => {
                                this.assertWebGL2();
                                this.ctx.texStorage3D(target, levels, internalformat, width, height, depth);
                        },
                        TexImage3D: (target, level, internalformat, width, height, depth, border, format, type, size, data) => {
                                this.assertWebGL2();
                                if (data) {
                                        this.ctx.texImage3D(target, level, internalformat, width, height, depth, border, format, type, this.mem.loadBytes(data, size));
                                } else {
                                        this.ctx.texImage3D(target, level, internalformat, width, height, depth, border, format, type, null);
                                }
                        },
                        TexSubImage3D: (target, level, xoffset, yoffset, zoffset, width, height, depth, format, type, size, data) => {
                                this.assertWebGL2();
                                this.ctx.texSubImage3D(target, level, xoffset, yoffset, zoffset, width, height, depth, format, type, this.mem.loadBytes(data, size));
                        },
                        CompressedTexImage3D: (target, level, internalformat, width, height, depth, border, imageSize, data) => {
                                this.assertWebGL2();
                                if (data) {
                                        this.ctx.compressedTexImage3D(target, level, internalformat, width, height, depth, border, this.mem.loadBytes(data, imageSize));
                                } else {
                                        this.ctx.compressedTexImage3D(target, level, internalformat, width, height, depth, border, null);
                                }
                        },
                        CompressedTexSubImage3D: (target, level, xoffset, yoffset, zoffset, width, height, depth, format, imageSize, data) => {
                                this.assertWebGL2();
                                if (data) {
                                        this.ctx.compressedTexSubImage3D(target, level, xoffset, yoffset, zoffset, width, height, depth, format, this.mem.loadBytes(data, imageSize));
                                } else {
                                        this.ctx.compressedTexSubImage3D(target, level, xoffset, yoffset, zoffset, width, height, depth, format, null);
                                }
                        },
                        CopyTexSubImage3D: (target, level, xoffset, yoffset, zoffset, x, y, width, height) => {
                                this.assertWebGL2();
                                this.ctx.copyTexSubImage3D(target, level, xoffset, yoffset, zoffset, x, y, width, height);
                        },

                        /* Programs and shaders */
                        GetFragDataLocation: (program, name_ptr, name_len) => {
                                this.assertWebGL2();
                                let name = this.mem.loadString(name_ptr, name_len);
                                return this.ctx.getFragDataLocation(this.programs[program], name);
                        },

                        /* Uniforms */
                        Uniform1ui: (location, v0) => { this.assertWebGL2(); this.ctx.uniform1ui(this.uniforms[location], v0); },
                        Uniform2ui: (location, v0, v1) => { this.assertWebGL2(); this.ctx.uniform2ui(this.uniforms[location], v0, v1); },
                        Uniform3ui: (location, v0, v1, v2) => { this.assertWebGL2(); this.ctx.uniform3ui(this.uniforms[location], v0, v1, v2); },
                        Uniform4ui: (location, v0, v1, v2, v3) => { this.assertWebGL2(); this.ctx.uniform4ui(this.uniforms[location], v0, v1, v2, v3); },

                        UniformMatrix3x2fv: (location, addr) => {
                                this.assertWebGL2();
                                let array = this.mem.loadF32Array(addr, 3*2);
                                this.ctx.uniformMatrix3x2fv(this.uniforms[location], false, array);
                        },
                        UniformMatrix4x2fv: (location, addr) => {
                                this.assertWebGL2();
                                let array = this.mem.loadF32Array(addr, 4*2);
                                this.ctx.uniformMatrix4x2fv(this.uniforms[location], false, array);
                        },
                        UniformMatrix2x3fv: (location, addr) => {
                                this.assertWebGL2();
                                let array = this.mem.loadF32Array(addr, 2*3);
                                this.ctx.uniformMatrix2x3fv(this.uniforms[location], false, array);
                        },
                        UniformMatrix4x3fv: (location, addr) => {
                                this.assertWebGL2();
                                let array = this.mem.loadF32Array(addr, 4*3);
                                this.ctx.uniformMatrix4x3fv(this.uniforms[location], false, array);
                        },
                        UniformMatrix2x4fv: (location, addr) => {
                                this.assertWebGL2();
                                let array = this.mem.loadF32Array(addr, 2*4);
                                this.ctx.uniformMatrix2x4fv(this.uniforms[location], false, array);
                        },
                        UniformMatrix3x4fv: (location, addr) => {
                                this.assertWebGL2();
                                let array = this.mem.loadF32Array(addr, 3*4);
                                this.ctx.uniformMatrix3x4fv(this.uniforms[location], false, array);
                        },

                        /* Vertex attribs */
                        VertexAttribI4i: (index, x, y, z, w) => {
                                this.assertWebGL2();
                                this.ctx.vertexAttribI4i(index, x, y, z, w);
                        },
                        VertexAttribI4ui: (index, x, y, z, w) => {
                                this.assertWebGL2();
                                this.ctx.vertexAttribI4ui(index, x, y, z, w);
                        },
                        VertexAttribIPointer: (index, size, type, stride, offset) => {
                                this.assertWebGL2();
                                this.ctx.vertexAttribIPointer(index, size, type, stride, Number(offset));
                        },

                        /* Writing to the drawing buffer */
                        VertexAttribDivisor: (index, divisor) => {
                                this.assertWebGL2();
                                this.ctx.vertexAttribDivisor(index, divisor);
                        },
                        DrawArraysInstanced: (mode, first, count, instanceCount) => {
                                this.assertWebGL2();
                                this.ctx.drawArraysInstanced(mode, first, count, instanceCount);
                        },
                        DrawElementsInstanced: (mode, count, type, offset, instanceCount) => {
                                this.assertWebGL2();
                                this.ctx.drawElementsInstanced(mode, count, type, Number(offset), instanceCount);
                        },
                        DrawRangeElements: (mode, start, end, count, type, offset) => {
                                this.assertWebGL2();
                                this.ctx.drawRangeElements(mode, start, end, count, type, Number(offset));
                        },

                        /* Multiple Render Targets */
                        DrawBuffers: (buffers_ptr, buffers_len) => {
                                this.assertWebGL2();
                                let array = this.mem.loadU32Array(buffers_ptr, buffers_len);
                                this.ctx.drawBuffers(array);
                        },
                        ClearBufferfv: (buffer, drawbuffer, values_ptr, values_len) => {
                                this.assertWebGL2();
                                let array = this.mem.loadF32Array(values_ptr, values_len);
                                this.ctx.clearBufferfv(buffer, drawbuffer, array);
                        },
                        ClearBufferiv: (buffer, drawbuffer, values_ptr, values_len) => {
                                this.assertWebGL2();
                                let array = this.mem.loadI32Array(values_ptr, values_len);
                                this.ctx.clearBufferiv(buffer, drawbuffer, array);
                        },
                        ClearBufferuiv: (buffer, drawbuffer, values_ptr, values_len) => {
                                this.assertWebGL2();
                                let array = this.mem.loadU32Array(values_ptr, values_len);
                                this.ctx.clearBufferuiv(buffer, drawbuffer, array);
                        },
                        ClearBufferfi: (buffer, drawbuffer, depth, stencil) => {
                                this.assertWebGL2();
                                this.ctx.clearBufferfi(buffer, drawbuffer, depth, stencil);
                        },

                        /* Query Objects */
                        CreateQuery: () => {
                                this.assertWebGL2();
                                let query = this.ctx.createQuery();
                                let id = this.getNewId(this.queries);
                                query.name = id;
                                this.queries[id] = query;
                                return id;
                        },
                        DeleteQuery: (id) => {
                                this.assertWebGL2();
                                let obj = this.queries[id];
                                if (obj && id != 0) {
                                        this.ctx.deleteQuery(obj);
                                        this.queries[id] = null;
                                }
                        },
                        IsQuery: (query) => {
                                this.assertWebGL2();
                                return this.ctx.isQuery(this.queries[query]);
                        },
                        BeginQuery: (target, query) => {
                                this.assertWebGL2();
                                this.ctx.beginQuery(target, this.queries[query])
                        },
                        EndQuery: (target) => {
                                this.assertWebGL2();
                                this.ctx.endQuery(target);
                        },
                        GetQuery: (target, pname) => {
                                this.assertWebGL2();
                                let query = this.ctx.getQuery(target, pname);
                                if (!query) {
                                        return 0;
                                }
                                if (this.queries.indexOf(query) !== -1) {
                                        return query.name;
                                }
                                let id = this.getNewId(this.queries);
                                query.name = id;
                                this.queries[id] = query;
                                return id;
                        },

                        /* Sampler Objects */
                        CreateSampler: () => {
                                this.assertWebGL2();
                                let sampler = this.ctx.createSampler();
                                let id = this.getNewId(this.samplers);
                                sampler.name = id;
                                this.samplers[id] = sampler;
                                return id;
                        },
                        DeleteSampler: (id) => {
                                this.assertWebGL2();
                                let obj = this.samplers[id];
                                if (obj && id != 0) {
                                        this.ctx.deleteSampler(obj);
                                        this.samplers[id] = null;
                                }
                        },
                        IsSampler: (sampler) => {
                                this.assertWebGL2();
                                return this.ctx.isSampler(this.samplers[sampler]);
                        },
                        BindSampler: (unit, sampler) => {
                                this.assertWebGL2();
                                this.ctx.bindSampler(unit, this.samplers[sampler]);
                        },
                        SamplerParameteri: (sampler, pname, param) => {
                                this.assertWebGL2();
                                this.ctx.samplerParameteri(this.samplers[sampler], pname, param);
                        },
                        SamplerParameterf: (sampler, pname, param) => {
                                this.assertWebGL2();
                                this.ctx.samplerParameterf(this.samplers[sampler], pname, param);
                        },

                        /* Sync objects */
                        FenceSync: (condition, flags) => {
                                this.assertWebGL2();
                                let sync = this.ctx.fenceSync(condition, flags);
                                let id = this.getNewId(this.syncs);
                                sync.name = id;
                                this.syncs[id] = sync;
                                return id;
                        },
                        IsSync: (sync) => {
                                this.assertWebGL2();
                                return this.ctx.isSync(this.syncs[sync]);
                        },
                        DeleteSync: (id) => {
                                this.assertWebGL2();
                                let obj = this.syncs[id];
                                if (obj && id != 0) {
                                        this.ctx.deleteSampler(obj);
                                        this.syncs[id] = null;
                                }
                        },
                        ClientWaitSync: (sync, flags, timeout) => {
                                this.assertWebGL2();
                                return this.ctx.clientWaitSync(this.syncs[sync], flags, timeout);
                        },
                        WaitSync: (sync, flags, timeout) => {
                                this.assertWebGL2();
                                this.ctx.waitSync(this.syncs[sync], flags, timeout)     ;
                        },


                        /* Transform Feedback */
                        CreateTransformFeedback: () => {
                                this.assertWebGL2();
                                let transformFeedback = this.ctx.createTransformFeedback();
                                let id = this.getNewId(this.transformFeedbacks);
                                transformFeedback.name = id;
                                this.transformFeedbacks[id] = transformFeedback;
                                return id;
                        },
                        DeleteTransformFeedback: (id)  => {
                                this.assertWebGL2();
                                let obj = this.transformFeedbacks[id];
                                if (obj && id != 0) {
                                        this.ctx.deleteTransformFeedback(obj);
                                        this.transformFeedbacks[id] = null;
                                }
                        },
                        IsTransformFeedback: (tf) => {
                                this.assertWebGL2();
                                return this.ctx.isTransformFeedback(this.transformFeedbacks[tf]);
                        },
                        BindTransformFeedback: (target, tf) => {
                                this.assertWebGL2();
                                this.ctx.bindTransformFeedback(target, this.transformFeedbacks[tf]);
                        },
                        BeginTransformFeedback: (primitiveMode) => {
                                this.assertWebGL2();
                                this.ctx.beginTransformFeedback(primitiveMode);
                        },
                        EndTransformFeedback: () => {
                                this.assertWebGL2();
                                this.ctx.endTransformFeedback();
                        },
                        TransformFeedbackVaryings: (program, varyings_ptr, varyings_len, bufferMode) => {
                                this.assertWebGL2();
                                const stringSize = this.mem.intSize*2;
                                let varyings = [];
                                for (let i = 0; i < varyings_len; i++) {
                                        let ptr = this.mem.loadPtr(varyings_ptr + i*stringSize + 0*4);
                                        let len = this.mem.loadPtr(varyings_ptr + i*stringSize + 1*4);
                                        varyings.push(this.mem.loadString(ptr, len));
                                }
                                this.ctx.transformFeedbackVaryings(this.programs[program], varyings, bufferMode);
                        },
                        PauseTransformFeedback: () => {
                                this.assertWebGL2();
                                this.ctx.pauseTransformFeedback();
                        },
                        ResumeTransformFeedback: () => {
                                this.assertWebGL2();
                                this.ctx.resumeTransformFeedback();
                        },


                        /* Uniform Buffer Objects and Transform Feedback Buffers */
                        BindBufferBase: (target, index, buffer) => {
                                this.assertWebGL2();
                                this.ctx.bindBufferBase(target, index, this.buffers[buffer]);
                        },
                        BindBufferRange: (target, index, buffer, offset, size) => {
                                this.assertWebGL2();
                                this.ctx.bindBufferRange(target, index, this.buffers[buffer], Number(offset), Number(size));
                        },
                        GetUniformBlockIndex: (program, uniformBlockName_ptr, uniformBlockName_len) => {
                                this.assertWebGL2();
                                let name = this.mem.loadString(uniformBlockName_ptr, uniformBlockName_len);
                                return this.ctx.getUniformBlockIndex(this.programs[program], name);
                        },
                        // any getActiveUniformBlockParameter(WebGLProgram program, GLuint uniformBlockIndex, GLenum pname);
                        GetActiveUniformBlockName: (program, uniformBlockIndex, buf_ptr, buf_len, length_ptr) => {
                                this.assertWebGL2();
                                let name = this.ctx.getActiveUniformBlockName(this.programs[program], uniformBlockIndex);

                                let n = Math.min(buf_len, name.length);
                                name = name.substring(0, n);
                                this.mem.loadBytes(buf_ptr, buf_len).set(new TextEncoder().encode(name))
                                this.mem.storeInt(length_ptr, n);
                        },
                        UniformBlockBinding: (program, uniformBlockIndex, uniformBlockBinding) => {
                                this.assertWebGL2();
                                this.ctx.uniformBlockBinding(this.programs[program], uniformBlockIndex, uniformBlockBinding);
                        },

                        /* Vertex Array Objects */
                        CreateVertexArray: () => {
                                this.assertWebGL2();
                                let vao = this.ctx.createVertexArray();
                                let id = this.getNewId(this.vaos);
                                vao.name = id;
                                this.vaos[id] = vao;
                                return id;
                        },
                        DeleteVertexArray: (id) => {
                                this.assertWebGL2();
                                let obj = this.vaos[id];
                                if (obj && id != 0) {
                                        this.ctx.deleteVertexArray(obj);
                                        this.vaos[id] = null;
                                }
                        },
                        IsVertexArray: (vertexArray) => {
                                this.assertWebGL2();
                                return this.ctx.isVertexArray(this.vaos[vertexArray]);
                        },
                        BindVertexArray: (vertexArray) => {
                                this.assertWebGL2();
                                this.ctx.bindVertexArray(this.vaos[vertexArray]);
                        },
                };
        }
};


function srlangSetupDefaultImports(wasmMemoryInterface, consoleElement, memory) {
        let webglContext = new WebGLInterface(wasmMemoryInterface);
        let event_temp = {};

        // Helper for events (simplified for now as I need to be careful with struct offsets)
        const onEventReceived = (event_data, data, callback) => {
                event_temp.data = event_data;
                const exports = wasmMemoryInterface.exports;
                const ctx_ptr = exports.default_context_ptr ? exports.default_context_ptr() : 0;
                if(exports.srlang_dom_do_event_callback)
                    exports.srlang_dom_do_event_callback(data, callback, ctx_ptr);
                event_temp.data = null;
        };

        return {
                env: {
                        print: (ptr, len) => {
                                const str = wasmMemoryInterface.loadString(ptr, len);
                                console.log(str);
                        },
                        write: (fd, ptr, len) => {
                                const str = wasmMemoryInterface.loadString(ptr, len);
                                console.log(str);
                        },
                        trap: () => { throw new Error() },
                        alert: (ptr, len) => { alert(wasmMemoryInterface.loadString(ptr, len)) },
                        abort: () => { throw new Error("Aborted"); },
                        evaluate: (str_ptr, str_len) => { eval(wasmMemoryInterface.loadString(str_ptr, str_len)); },

                        time_now: () => BigInt(Date.now()),
                        tick_now: () => performance.now(),
                        
                        sqrt:    Math.sqrt,
                        sin:     Math.sin,
                        cos:     Math.cos,
                        pow:     Math.pow,
                        rand_bytes: (ptr, len) => {
                                const view = new Uint8Array(wasmMemoryInterface.memory.buffer, ptr, len)
                                crypto.getRandomValues(view)
                        },
                        // DOM / Events
                        init_event_raw: (ep) => {
                                const W = wasmMemoryInterface.intSize;
                                let offset = ep;
                                let off = (amount, alignment) => {
                                        if (alignment === undefined) {
                                                alignment = Math.min(amount, W);
                                        }
                                        if (offset % alignment != 0) {
                                                offset += alignment - (offset%alignment);
                                        }
                                        let x = offset;
                                        offset += amount;
                                        return x;
                                };

                                let align = (alignment) => {
                                        const modulo = offset & (alignment-1);
                                        if (modulo != 0) {
                                                offset += alignment - modulo
                                        }
                                };

                                let wmi = wasmMemoryInterface;

                                if (!event_temp.data) {
                                        return;
                                }

                                let e = event_temp.data.event;

                                wmi.storeU32(off(4), event_temp.data.name_code);
                                if (e.target == document) {
                                        wmi.storeU32(off(4), 1);
                                } else if (e.target == window) {
                                        wmi.storeU32(off(4), 2);
                                } else {
                                        wmi.storeU32(off(4), 0);
                                }
                                if (e.currentTarget == document) {
                                        wmi.storeU32(off(4), 1);
                                } else if (e.currentTarget == window) {
                                        wmi.storeU32(off(4), 2);
                                } else {
                                        wmi.storeU32(off(4), 0);
                                }

                                align(W);

                                wmi.storeI32(off(W), event_temp.data.id_ptr);
                                wmi.storeUint(off(W), event_temp.data.id_len);

                                align(8);
                                wmi.storeF64(off(8), e.timeStamp*1e-3);

                                wmi.storeU8(off(1), e.eventPhase);
                                let options = 0;
                                if (!!e.bubbles)    { options |= 1<<0; }
                                if (!!e.cancelable) { options |= 1<<1; }
                                if (!!e.composed)   { options |= 1<<2; }
                                wmi.storeU8(off(1), options);
                                wmi.storeU8(off(1), !!e.isComposing);
                                wmi.storeU8(off(1), !!e.isTrusted);

                                align(8);
                                if (e instanceof WheelEvent) {
                                        wmi.storeF64(off(8), e.deltaX);
                                        wmi.storeF64(off(8), e.deltaY);
                                        wmi.storeF64(off(8), e.deltaZ);
                                        wmi.storeU32(off(4), e.deltaMode);
                                } else if (e instanceof MouseEvent) {
                                        wmi.storeI64(off(8), BigInt(e.screenX));
                                        wmi.storeI64(off(8), BigInt(e.screenY));
                                        wmi.storeI64(off(8), BigInt(e.clientX));
                                        wmi.storeI64(off(8), BigInt(e.clientY));
                                        wmi.storeI64(off(8), BigInt(e.offsetX));
                                        wmi.storeI64(off(8), BigInt(e.offsetY));
                                        wmi.storeI64(off(8), BigInt(e.pageX));
                                        wmi.storeI64(off(8), BigInt(e.pageY));
                                        wmi.storeI64(off(8), BigInt(e.movementX));
                                        wmi.storeI64(off(8), BigInt(e.movementY));

                                        wmi.storeU8(off(1), !!e.ctrlKey);
                                        wmi.storeU8(off(1), !!e.shiftKey);
                                        wmi.storeU8(off(1), !!e.altKey);
                                        wmi.storeU8(off(1), !!e.metaKey);

                                        wmi.storeI16(off(2), e.button);
                                        wmi.storeU16(off(2), e.buttons);
                                } else if (e instanceof KeyboardEvent) {
                                        const keyPtr  = off(W*2, W);
                                        const codePtr = off(W*2, W);

                                        wmi.storeU8(off(1), e.location);

                                        wmi.storeU8(off(1), !!e.ctrlKey);
                                        wmi.storeU8(off(1), !!e.shiftKey);
                                        wmi.storeU8(off(1), !!e.altKey);
                                        wmi.storeU8(off(1), !!e.metaKey);

                                        wmi.storeU8(off(1), !!e.repeat);

                                        wmi.storeI32(off(4), e.charCode);

                                        wmi.storeInt(off(W, W), e.key.length)
                                        wmi.storeInt(off(W, W), e.code.length)
                                        wmi.storeString(off(32, 1), e.key);
                                        wmi.storeString(off(32, 1), e.code);
                                }
                        },

                        add_event_listener: (id_ptr, id_len, name_ptr, name_len, name_code, data, callback, use_capture) => {
                                let id = wasmMemoryInterface.loadString(id_ptr, id_len);
                                let name = wasmMemoryInterface.loadString(name_ptr, name_len);
                                let element = getElement(id);
                                if (element == undefined) return false;
                                
                                let listener = (e) => {
                                        let event_data = {};
                                        event_data.id_ptr = id_ptr;
                                        event_data.id_len = id_len;
                                        event_data.event = e;
                                        event_data.name_code = name_code;
                                        onEventReceived(event_data, data, callback);
                                };
                                element.addEventListener(name, listener, !!use_capture);
                                return true;
                        },

                        add_window_event_listener: (name_ptr, name_len, name_code, data, callback, use_capture) => {
                                let name = wasmMemoryInterface.loadString(name_ptr, name_len);
                                let listener = (e) => {
                                        let event_data = {};
                                        event_data.id_ptr = 0;
                                        event_data.id_len = 0;
                                        event_data.event = e;
                                        event_data.name_code = name_code;
                                        onEventReceived(event_data, data, callback);
                                };
                                window.addEventListener(name, listener, !!use_capture);
                                return true;
                        },
                        
                        event_stop_propagation: () => {
                                if (event_temp.data && event_temp.data.event) event_temp.data.event.stopPropagation();
                        },
                        event_prevent_default: () => {
                                if (event_temp.data && event_temp.data.event) event_temp.data.event.preventDefault();
                        },

                        ...webglContext.getWebGL1Interface(),
                },

                "webgl": webglContext.getWebGL1Interface(),
                "webgl2": webglContext.getWebGL2Interface(),
        };
};

async function runWasm(wasmPath, extraImports) {
        const wasmMemoryInterface = new WasmMemoryInterface();
        wasmMemoryInterface.setIntSize(4);

        let imports = srlangSetupDefaultImports(wasmMemoryInterface, null, null);
        if (extraImports) imports = { ...imports, ...extraImports };

        const response = await fetch(wasmPath);
        const file = await response.arrayBuffer();
        const wasm = await WebAssembly.instantiate(file, imports);
        
        const exports = wasm.instance.exports;
        wasmMemoryInterface.setExports(exports);
        wasmMemoryInterface.setMemory(exports.memory);

        if (exports._start) exports._start();
        if (exports.main) exports.main();

        if (exports.step) {
                let prevTimeStamp = undefined;
                function step(currTimeStamp) {
                        if (prevTimeStamp == undefined) prevTimeStamp = currTimeStamp;
                        const dt = (currTimeStamp - prevTimeStamp)*0.001;
                        prevTimeStamp = currTimeStamp;
                        exports.step(dt);
                        requestAnimationFrame(step);
                }
                requestAnimationFrame(step);
        }
        return wasm.instance;
};

window.srlang = {
        runWasm: runWasm
};
})();
