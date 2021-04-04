(function () {
/** vim: et:ts=4:sw=4:sts=4
 * @license RequireJS 2.1.22 Copyright (c) 2010-2015, The Dojo Foundation All Rights Reserved.
 * Available via the MIT or new BSD license.
 * see: http://github.com/jrburke/requirejs for details
 */
//Not using strict: uneven strict support in browsers, #392, and causes
//problems with requirejs.exec()/transpiler plugins that may not be strict.
/*jslint regexp: true, nomen: true, sloppy: true */
/*global window, navigator, document, importScripts, setTimeout, opera */

var requirejs, require, define;
(function (global) {
    var req, s, head, baseElement, dataMain, src,
        interactiveScript, currentlyAddingScript, mainScript, subPath,
        version = '2.1.22',
        commentRegExp = /(\/\*([\s\S]*?)\*\/|([^:]|^)\/\/(.*)$)/mg,
        cjsRequireRegExp = /[^.]\s*require\s*\(\s*["']([^'"\s]+)["']\s*\)/g,
        jsSuffixRegExp = /\.js$/,
        currDirRegExp = /^\.\//,
        op = Object.prototype,
        ostring = op.toString,
        hasOwn = op.hasOwnProperty,
        ap = Array.prototype,
        isBrowser = !!(typeof window !== 'undefined' && typeof navigator !== 'undefined' && window.document),
        isWebWorker = !isBrowser && typeof importScripts !== 'undefined',
        //PS3 indicates loaded and complete, but need to wait for complete
        //specifically. Sequence is 'loading', 'loaded', execution,
        // then 'complete'. The UA check is unfortunate, but not sure how
        //to feature test w/o causing perf issues.
        readyRegExp = isBrowser && navigator.platform === 'PLAYSTATION 3' ?
                      /^complete$/ : /^(complete|loaded)$/,
        defContextName = '_',
        //Oh the tragedy, detecting opera. See the usage of isOpera for reason.
        isOpera = typeof opera !== 'undefined' && opera.toString() === '[object Opera]',
        contexts = {},
        cfg = {},
        globalDefQueue = [],
        useInteractive = false;

    function isFunction(it) {
        return ostring.call(it) === '[object Function]';
    }

    function isArray(it) {
        return ostring.call(it) === '[object Array]';
    }

    /**
     * Helper function for iterating over an array. If the func returns
     * a true value, it will break out of the loop.
     */
    function each(ary, func) {
        if (ary) {
            var i;
            for (i = 0; i < ary.length; i += 1) {
                if (ary[i] && func(ary[i], i, ary)) {
                    break;
                }
            }
        }
    }

    /**
     * Helper function for iterating over an array backwards. If the func
     * returns a true value, it will break out of the loop.
     */
    function eachReverse(ary, func) {
        if (ary) {
            var i;
            for (i = ary.length - 1; i > -1; i -= 1) {
                if (ary[i] && func(ary[i], i, ary)) {
                    break;
                }
            }
        }
    }

    function hasProp(obj, prop) {
        return hasOwn.call(obj, prop);
    }

    function getOwn(obj, prop) {
        return hasProp(obj, prop) && obj[prop];
    }

    /**
     * Cycles over properties in an object and calls a function for each
     * property value. If the function returns a truthy value, then the
     * iteration is stopped.
     */
    function eachProp(obj, func) {
        var prop;
        for (prop in obj) {
            if (hasProp(obj, prop)) {
                if (func(obj[prop], prop)) {
                    break;
                }
            }
        }
    }

    /**
     * Simple function to mix in properties from source into target,
     * but only if target does not already have a property of the same name.
     */
    function mixin(target, source, force, deepStringMixin) {
        if (source) {
            eachProp(source, function (value, prop) {
                if (force || !hasProp(target, prop)) {
                    if (deepStringMixin && typeof value === 'object' && value &&
                        !isArray(value) && !isFunction(value) &&
                        !(value instanceof RegExp)) {

                        if (!target[prop]) {
                            target[prop] = {};
                        }
                        mixin(target[prop], value, force, deepStringMixin);
                    } else {
                        target[prop] = value;
                    }
                }
            });
        }
        return target;
    }

    //Similar to Function.prototype.bind, but the 'this' object is specified
    //first, since it is easier to read/figure out what 'this' will be.
    function bind(obj, fn) {
        return function () {
            return fn.apply(obj, arguments);
        };
    }

    function scripts() {
        return document.getElementsByTagName('script');
    }

    function defaultOnError(err) {
        throw err;
    }

    //Allow getting a global that is expressed in
    //dot notation, like 'a.b.c'.
    function getGlobal(value) {
        if (!value) {
            return value;
        }
        var g = global;
        each(value.split('.'), function (part) {
            g = g[part];
        });
        return g;
    }

    /**
     * Constructs an error with a pointer to an URL with more information.
     * @param {String} id the error ID that maps to an ID on a web page.
     * @param {String} message human readable error.
     * @param {Error} [err] the original error, if there is one.
     *
     * @returns {Error}
     */
    function makeError(id, msg, err, requireModules) {
        var e = new Error(msg + '\nhttp://requirejs.org/docs/errors.html#' + id);
        e.requireType = id;
        e.requireModules = requireModules;
        if (err) {
            e.originalError = err;
        }
        return e;
    }

    if (typeof define !== 'undefined') {
        //If a define is already in play via another AMD loader,
        //do not overwrite.
        return;
    }

    if (typeof requirejs !== 'undefined') {
        if (isFunction(requirejs)) {
            //Do not overwrite an existing requirejs instance.
            return;
        }
        cfg = requirejs;
        requirejs = undefined;
    }

    //Allow for a require config object
    if (typeof require !== 'undefined' && !isFunction(require)) {
        //assume it is a config object.
        cfg = require;
        require = undefined;
    }

    function newContext(contextName) {
        var inCheckLoaded, Module, context, handlers,
            checkLoadedTimeoutId,
            config = {
                //Defaults. Do not set a default for map
                //config to speed up normalize(), which
                //will run faster if there is no default.
                waitSeconds: 7,
                baseUrl: './',
                paths: {},
                bundles: {},
                pkgs: {},
                shim: {},
                config: {}
            },
            registry = {},
            //registry of just enabled modules, to speed
            //cycle breaking code when lots of modules
            //are registered, but not activated.
            enabledRegistry = {},
            undefEvents = {},
            defQueue = [],
            defined = {},
            urlFetched = {},
            bundlesMap = {},
            requireCounter = 1,
            unnormalizedCounter = 1;

        /**
         * Trims the . and .. from an array of path segments.
         * It will keep a leading path segment if a .. will become
         * the first path segment, to help with module name lookups,
         * which act like paths, but can be remapped. But the end result,
         * all paths that use this function should look normalized.
         * NOTE: this method MODIFIES the input array.
         * @param {Array} ary the array of path segments.
         */
        function trimDots(ary) {
            var i, part;
            for (i = 0; i < ary.length; i++) {
                part = ary[i];
                if (part === '.') {
                    ary.splice(i, 1);
                    i -= 1;
                } else if (part === '..') {
                    // If at the start, or previous value is still ..,
                    // keep them so that when converted to a path it may
                    // still work when converted to a path, even though
                    // as an ID it is less than ideal. In larger point
                    // releases, may be better to just kick out an error.
                    if (i === 0 || (i === 1 && ary[2] === '..') || ary[i - 1] === '..') {
                        continue;
                    } else if (i > 0) {
                        ary.splice(i - 1, 2);
                        i -= 2;
                    }
                }
            }
        }

        /**
         * Given a relative module name, like ./something, normalize it to
         * a real name that can be mapped to a path.
         * @param {String} name the relative name
         * @param {String} baseName a real name that the name arg is relative
         * to.
         * @param {Boolean} applyMap apply the map config to the value. Should
         * only be done if this normalization is for a dependency ID.
         * @returns {String} normalized name
         */
        function normalize(name, baseName, applyMap) {
            var pkgMain, mapValue, nameParts, i, j, nameSegment, lastIndex,
                foundMap, foundI, foundStarMap, starI, normalizedBaseParts,
                baseParts = (baseName && baseName.split('/')),
                map = config.map,
                starMap = map && map['*'];

            //Adjust any relative paths.
            if (name) {
                name = name.split('/');
                lastIndex = name.length - 1;

                // If wanting node ID compatibility, strip .js from end
                // of IDs. Have to do this here, and not in nameToUrl
                // because node allows either .js or non .js to map
                // to same file.
                if (config.nodeIdCompat && jsSuffixRegExp.test(name[lastIndex])) {
                    name[lastIndex] = name[lastIndex].replace(jsSuffixRegExp, '');
                }

                // Starts with a '.' so need the baseName
                if (name[0].charAt(0) === '.' && baseParts) {
                    //Convert baseName to array, and lop off the last part,
                    //so that . matches that 'directory' and not name of the baseName's
                    //module. For instance, baseName of 'one/two/three', maps to
                    //'one/two/three.js', but we want the directory, 'one/two' for
                    //this normalization.
                    normalizedBaseParts = baseParts.slice(0, baseParts.length - 1);
                    name = normalizedBaseParts.concat(name);
                }

                trimDots(name);
                name = name.join('/');
            }

            //Apply map config if available.
            if (applyMap && map && (baseParts || starMap)) {
                nameParts = name.split('/');

                outerLoop: for (i = nameParts.length; i > 0; i -= 1) {
                    nameSegment = nameParts.slice(0, i).join('/');

                    if (baseParts) {
                        //Find the longest baseName segment match in the config.
                        //So, do joins on the biggest to smallest lengths of baseParts.
                        for (j = baseParts.length; j > 0; j -= 1) {
                            mapValue = getOwn(map, baseParts.slice(0, j).join('/'));

                            //baseName segment has config, find if it has one for
                            //this name.
                            if (mapValue) {
                                mapValue = getOwn(mapValue, nameSegment);
                                if (mapValue) {
                                    //Match, update name to the new value.
                                    foundMap = mapValue;
                                    foundI = i;
                                    break outerLoop;
                                }
                            }
                        }
                    }

                    //Check for a star map match, but just hold on to it,
                    //if there is a shorter segment match later in a matching
                    //config, then favor over this star map.
                    if (!foundStarMap && starMap && getOwn(starMap, nameSegment)) {
                        foundStarMap = getOwn(starMap, nameSegment);
                        starI = i;
                    }
                }

                if (!foundMap && foundStarMap) {
                    foundMap = foundStarMap;
                    foundI = starI;
                }

                if (foundMap) {
                    nameParts.splice(0, foundI, foundMap);
                    name = nameParts.join('/');
                }
            }

            // If the name points to a package's name, use
            // the package main instead.
            pkgMain = getOwn(config.pkgs, name);

            return pkgMain ? pkgMain : name;
        }

        function removeScript(name) {
            if (isBrowser) {
                each(scripts(), function (scriptNode) {
                    if (scriptNode.getAttribute('data-requiremodule') === name &&
                            scriptNode.getAttribute('data-requirecontext') === context.contextName) {
                        scriptNode.parentNode.removeChild(scriptNode);
                        return true;
                    }
                });
            }
        }

        function hasPathFallback(id) {
            var pathConfig = getOwn(config.paths, id);
            if (pathConfig && isArray(pathConfig) && pathConfig.length > 1) {
                //Pop off the first array value, since it failed, and
                //retry
                pathConfig.shift();
                context.require.undef(id);

                //Custom require that does not do map translation, since
                //ID is "absolute", already mapped/resolved.
                context.makeRequire(null, {
                    skipMap: true
                })([id]);

                return true;
            }
        }

        //Turns a plugin!resource to [plugin, resource]
        //with the plugin being undefined if the name
        //did not have a plugin prefix.
        function splitPrefix(name) {
            var prefix,
                index = name ? name.indexOf('!') : -1;
            if (index > -1) {
                prefix = name.substring(0, index);
                name = name.substring(index + 1, name.length);
            }
            return [prefix, name];
        }

        /**
         * Creates a module mapping that includes plugin prefix, module
         * name, and path. If parentModuleMap is provided it will
         * also normalize the name via require.normalize()
         *
         * @param {String} name the module name
         * @param {String} [parentModuleMap] parent module map
         * for the module name, used to resolve relative names.
         * @param {Boolean} isNormalized: is the ID already normalized.
         * This is true if this call is done for a define() module ID.
         * @param {Boolean} applyMap: apply the map config to the ID.
         * Should only be true if this map is for a dependency.
         *
         * @returns {Object}
         */
        function makeModuleMap(name, parentModuleMap, isNormalized, applyMap) {
            var url, pluginModule, suffix, nameParts,
                prefix = null,
                parentName = parentModuleMap ? parentModuleMap.name : null,
                originalName = name,
                isDefine = true,
                normalizedName = '';

            //If no name, then it means it is a require call, generate an
            //internal name.
            if (!name) {
                isDefine = false;
                name = '_@r' + (requireCounter += 1);
            }

            nameParts = splitPrefix(name);
            prefix = nameParts[0];
            name = nameParts[1];

            if (prefix) {
                prefix = normalize(prefix, parentName, applyMap);
                pluginModule = getOwn(defined, prefix);
            }

            //Account for relative paths if there is a base name.
            if (name) {
                if (prefix) {
                    if (pluginModule && pluginModule.normalize) {
                        //Plugin is loaded, use its normalize method.
                        normalizedName = pluginModule.normalize(name, function (name) {
                            return normalize(name, parentName, applyMap);
                        });
                    } else {
                        // If nested plugin references, then do not try to
                        // normalize, as it will not normalize correctly. This
                        // places a restriction on resourceIds, and the longer
                        // term solution is not to normalize until plugins are
                        // loaded and all normalizations to allow for async
                        // loading of a loader plugin. But for now, fixes the
                        // common uses. Details in #1131
                        normalizedName = name.indexOf('!') === -1 ?
                                         normalize(name, parentName, applyMap) :
                                         name;
                    }
                } else {
                    //A regular module.
                    normalizedName = normalize(name, parentName, applyMap);

                    //Normalized name may be a plugin ID due to map config
                    //application in normalize. The map config values must
                    //already be normalized, so do not need to redo that part.
                    nameParts = splitPrefix(normalizedName);
                    prefix = nameParts[0];
                    normalizedName = nameParts[1];
                    isNormalized = true;

                    url = context.nameToUrl(normalizedName);
                }
            }

            //If the id is a plugin id that cannot be determined if it needs
            //normalization, stamp it with a unique ID so two matching relative
            //ids that may conflict can be separate.
            suffix = prefix && !pluginModule && !isNormalized ?
                     '_unnormalized' + (unnormalizedCounter += 1) :
                     '';

            return {
                prefix: prefix,
                name: normalizedName,
                parentMap: parentModuleMap,
                unnormalized: !!suffix,
                url: url,
                originalName: originalName,
                isDefine: isDefine,
                id: (prefix ?
                        prefix + '!' + normalizedName :
                        normalizedName) + suffix
            };
        }

        function getModule(depMap) {
            var id = depMap.id,
                mod = getOwn(registry, id);

            if (!mod) {
                mod = registry[id] = new context.Module(depMap);
            }

            return mod;
        }

        function on(depMap, name, fn) {
            var id = depMap.id,
                mod = getOwn(registry, id);

            if (hasProp(defined, id) &&
                    (!mod || mod.defineEmitComplete)) {
                if (name === 'defined') {
                    fn(defined[id]);
                }
            } else {
                mod = getModule(depMap);
                if (mod.error && name === 'error') {
                    fn(mod.error);
                } else {
                    mod.on(name, fn);
                }
            }
        }

        function onError(err, errback) {
            var ids = err.requireModules,
                notified = false;

            if (errback) {
                errback(err);
            } else {
                each(ids, function (id) {
                    var mod = getOwn(registry, id);
                    if (mod) {
                        //Set error on module, so it skips timeout checks.
                        mod.error = err;
                        if (mod.events.error) {
                            notified = true;
                            mod.emit('error', err);
                        }
                    }
                });

                if (!notified) {
                    req.onError(err);
                }
            }
        }

        /**
         * Internal method to transfer globalQueue items to this context's
         * defQueue.
         */
        function takeGlobalQueue() {
            //Push all the globalDefQueue items into the context's defQueue
            if (globalDefQueue.length) {
                each(globalDefQueue, function(queueItem) {
                    var id = queueItem[0];
                    if (typeof id === 'string') {
                        context.defQueueMap[id] = true;
                    }
                    defQueue.push(queueItem);
                });
                globalDefQueue = [];
            }
        }

        handlers = {
            'require': function (mod) {
                if (mod.require) {
                    return mod.require;
                } else {
                    return (mod.require = context.makeRequire(mod.map));
                }
            },
            'exports': function (mod) {
                mod.usingExports = true;
                if (mod.map.isDefine) {
                    if (mod.exports) {
                        return (defined[mod.map.id] = mod.exports);
                    } else {
                        return (mod.exports = defined[mod.map.id] = {});
                    }
                }
            },
            'module': function (mod) {
                if (mod.module) {
                    return mod.module;
                } else {
                    return (mod.module = {
                        id: mod.map.id,
                        uri: mod.map.url,
                        config: function () {
                            return getOwn(config.config, mod.map.id) || {};
                        },
                        exports: mod.exports || (mod.exports = {})
                    });
                }
            }
        };

        function cleanRegistry(id) {
            //Clean up machinery used for waiting modules.
            delete registry[id];
            delete enabledRegistry[id];
        }

        function breakCycle(mod, traced, processed) {
            var id = mod.map.id;

            if (mod.error) {
                mod.emit('error', mod.error);
            } else {
                traced[id] = true;
                each(mod.depMaps, function (depMap, i) {
                    var depId = depMap.id,
                        dep = getOwn(registry, depId);

                    //Only force things that have not completed
                    //being defined, so still in the registry,
                    //and only if it has not been matched up
                    //in the module already.
                    if (dep && !mod.depMatched[i] && !processed[depId]) {
                        if (getOwn(traced, depId)) {
                            mod.defineDep(i, defined[depId]);
                            mod.check(); //pass false?
                        } else {
                            breakCycle(dep, traced, processed);
                        }
                    }
                });
                processed[id] = true;
            }
        }

        function checkLoaded() {
            var err, usingPathFallback,
                waitInterval = config.waitSeconds * 1000,
                //It is possible to disable the wait interval by using waitSeconds of 0.
                expired = waitInterval && (context.startTime + waitInterval) < new Date().getTime(),
                noLoads = [],
                reqCalls = [],
                stillLoading = false,
                needCycleCheck = true;

            //Do not bother if this call was a result of a cycle break.
            if (inCheckLoaded) {
                return;
            }

            inCheckLoaded = true;

            //Figure out the state of all the modules.
            eachProp(enabledRegistry, function (mod) {
                var map = mod.map,
                    modId = map.id;

                //Skip things that are not enabled or in error state.
                if (!mod.enabled) {
                    return;
                }

                if (!map.isDefine) {
                    reqCalls.push(mod);
                }

                if (!mod.error) {
                    //If the module should be executed, and it has not
                    //been inited and time is up, remember it.
                    if (!mod.inited && expired) {
                        if (hasPathFallback(modId)) {
                            usingPathFallback = true;
                            stillLoading = true;
                        } else {
                            noLoads.push(modId);
                            removeScript(modId);
                        }
                    } else if (!mod.inited && mod.fetched && map.isDefine) {
                        stillLoading = true;
                        if (!map.prefix) {
                            //No reason to keep looking for unfinished
                            //loading. If the only stillLoading is a
                            //plugin resource though, keep going,
                            //because it may be that a plugin resource
                            //is waiting on a non-plugin cycle.
                            return (needCycleCheck = false);
                        }
                    }
                }
            });

            if (expired && noLoads.length) {
                //If wait time expired, throw error of unloaded modules.
                err = makeError('timeout', 'Load timeout for modules: ' + noLoads, null, noLoads);
                err.contextName = context.contextName;
                return onError(err);
            }

            //Not expired, check for a cycle.
            if (needCycleCheck) {
                each(reqCalls, function (mod) {
                    breakCycle(mod, {}, {});
                });
            }

            //If still waiting on loads, and the waiting load is something
            //other than a plugin resource, or there are still outstanding
            //scripts, then just try back later.
            if ((!expired || usingPathFallback) && stillLoading) {
                //Something is still waiting to load. Wait for it, but only
                //if a timeout is not already in effect.
                if ((isBrowser || isWebWorker) && !checkLoadedTimeoutId) {
                    checkLoadedTimeoutId = setTimeout(function () {
                        checkLoadedTimeoutId = 0;
                        checkLoaded();
                    }, 50);
                }
            }

            inCheckLoaded = false;
        }

        Module = function (map) {
            this.events = getOwn(undefEvents, map.id) || {};
            this.map = map;
            this.shim = getOwn(config.shim, map.id);
            this.depExports = [];
            this.depMaps = [];
            this.depMatched = [];
            this.pluginMaps = {};
            this.depCount = 0;

            /* this.exports this.factory
               this.depMaps = [],
               this.enabled, this.fetched
            */
        };

        Module.prototype = {
            init: function (depMaps, factory, errback, options) {
                options = options || {};

                //Do not do more inits if already done. Can happen if there
                //are multiple define calls for the same module. That is not
                //a normal, common case, but it is also not unexpected.
                if (this.inited) {
                    return;
                }

                this.factory = factory;

                if (errback) {
                    //Register for errors on this module.
                    this.on('error', errback);
                } else if (this.events.error) {
                    //If no errback already, but there are error listeners
                    //on this module, set up an errback to pass to the deps.
                    errback = bind(this, function (err) {
                        this.emit('error', err);
                    });
                }

                //Do a copy of the dependency array, so that
                //source inputs are not modified. For example
                //"shim" deps are passed in here directly, and
                //doing a direct modification of the depMaps array
                //would affect that config.
                this.depMaps = depMaps && depMaps.slice(0);

                this.errback = errback;

                //Indicate this module has be initialized
                this.inited = true;

                this.ignore = options.ignore;

                //Could have option to init this module in enabled mode,
                //or could have been previously marked as enabled. However,
                //the dependencies are not known until init is called. So
                //if enabled previously, now trigger dependencies as enabled.
                if (options.enabled || this.enabled) {
                    //Enable this module and dependencies.
                    //Will call this.check()
                    this.enable();
                } else {
                    this.check();
                }
            },

            defineDep: function (i, depExports) {
                //Because of cycles, defined callback for a given
                //export can be called more than once.
                if (!this.depMatched[i]) {
                    this.depMatched[i] = true;
                    this.depCount -= 1;
                    this.depExports[i] = depExports;
                }
            },

            fetch: function () {
                if (this.fetched) {
                    return;
                }
                this.fetched = true;

                context.startTime = (new Date()).getTime();

                var map = this.map;

                //If the manager is for a plugin managed resource,
                //ask the plugin to load it now.
                if (this.shim) {
                    context.makeRequire(this.map, {
                        enableBuildCallback: true
                    })(this.shim.deps || [], bind(this, function () {
                        return map.prefix ? this.callPlugin() : this.load();
                    }));
                } else {
                    //Regular dependency.
                    return map.prefix ? this.callPlugin() : this.load();
                }
            },

            load: function () {
                var url = this.map.url;

                //Regular dependency.
                if (!urlFetched[url]) {
                    urlFetched[url] = true;
                    context.load(this.map.id, url);
                }
            },

            /**
             * Checks if the module is ready to define itself, and if so,
             * define it.
             */
            check: function () {
                if (!this.enabled || this.enabling) {
                    return;
                }

                var err, cjsModule,
                    id = this.map.id,
                    depExports = this.depExports,
                    exports = this.exports,
                    factory = this.factory;

                if (!this.inited) {
                    // Only fetch if not already in the defQueue.
                    if (!hasProp(context.defQueueMap, id)) {
                        this.fetch();
                    }
                } else if (this.error) {
                    this.emit('error', this.error);
                } else if (!this.defining) {
                    //The factory could trigger another require call
                    //that would result in checking this module to
                    //define itself again. If already in the process
                    //of doing that, skip this work.
                    this.defining = true;

                    if (this.depCount < 1 && !this.defined) {
                        if (isFunction(factory)) {
                            try {
                                exports = context.execCb(id, factory, depExports, exports);
                            } catch (e) {
                                err = e;
                            }

                            // Favor return value over exports. If node/cjs in play,
                            // then will not have a return value anyway. Favor
                            // module.exports assignment over exports object.
                            if (this.map.isDefine && exports === undefined) {
                                cjsModule = this.module;
                                if (cjsModule) {
                                    exports = cjsModule.exports;
                                } else if (this.usingExports) {
                                    //exports already set the defined value.
                                    exports = this.exports;
                                }
                            }

                            if (err) {
                                // If there is an error listener, favor passing
                                // to that instead of throwing an error. However,
                                // only do it for define()'d  modules. require
                                // errbacks should not be called for failures in
                                // their callbacks (#699). However if a global
                                // onError is set, use that.
                                if ((this.events.error && this.map.isDefine) ||
                                    req.onError !== defaultOnError) {
                                    err.requireMap = this.map;
                                    err.requireModules = this.map.isDefine ? [this.map.id] : null;
                                    err.requireType = this.map.isDefine ? 'define' : 'require';
                                    return onError((this.error = err));
                                } else if (typeof console !== 'undefined' &&
                                           console.error) {
                                    // Log the error for debugging. If promises could be
                                    // used, this would be different, but making do.
                                    console.error(err);
                                } else {
                                    // Do not want to completely lose the error. While this
                                    // will mess up processing and lead to similar results
                                    // as bug 1440, it at least surfaces the error.
                                    req.onError(err);
                                }
                            }
                        } else {
                            //Just a literal value
                            exports = factory;
                        }

                        this.exports = exports;

                        if (this.map.isDefine && !this.ignore) {
                            defined[id] = exports;

                            if (req.onResourceLoad) {
                                var resLoadMaps = [];
                                each(this.depMaps, function (depMap) {
                                    resLoadMaps.push(depMap.normalizedMap || depMap);
                                });
                                req.onResourceLoad(context, this.map, resLoadMaps);
                            }
                        }

                        //Clean up
                        cleanRegistry(id);

                        this.defined = true;
                    }

                    //Finished the define stage. Allow calling check again
                    //to allow define notifications below in the case of a
                    //cycle.
                    this.defining = false;

                    if (this.defined && !this.defineEmitted) {
                        this.defineEmitted = true;
                        this.emit('defined', this.exports);
                        this.defineEmitComplete = true;
                    }

                }
            },

            callPlugin: function () {
                var map = this.map,
                    id = map.id,
                    //Map already normalized the prefix.
                    pluginMap = makeModuleMap(map.prefix);

                //Mark this as a dependency for this plugin, so it
                //can be traced for cycles.
                this.depMaps.push(pluginMap);

                on(pluginMap, 'defined', bind(this, function (plugin) {
                    var load, normalizedMap, normalizedMod,
                        bundleId = getOwn(bundlesMap, this.map.id),
                        name = this.map.name,
                        parentName = this.map.parentMap ? this.map.parentMap.name : null,
                        localRequire = context.makeRequire(map.parentMap, {
                            enableBuildCallback: true
                        });

                    //If current map is not normalized, wait for that
                    //normalized name to load instead of continuing.
                    if (this.map.unnormalized) {
                        //Normalize the ID if the plugin allows it.
                        if (plugin.normalize) {
                            name = plugin.normalize(name, function (name) {
                                return normalize(name, parentName, true);
                            }) || '';
                        }

                        //prefix and name should already be normalized, no need
                        //for applying map config again either.
                        normalizedMap = makeModuleMap(map.prefix + '!' + name,
                                                      this.map.parentMap);
                        on(normalizedMap,
                            'defined', bind(this, function (value) {
                                this.map.normalizedMap = normalizedMap;
                                this.init([], function () { return value; }, null, {
                                    enabled: true,
                                    ignore: true
                                });
                            }));

                        normalizedMod = getOwn(registry, normalizedMap.id);
                        if (normalizedMod) {
                            //Mark this as a dependency for this plugin, so it
                            //can be traced for cycles.
                            this.depMaps.push(normalizedMap);

                            if (this.events.error) {
                                normalizedMod.on('error', bind(this, function (err) {
                                    this.emit('error', err);
                                }));
                            }
                            normalizedMod.enable();
                        }

                        return;
                    }

                    //If a paths config, then just load that file instead to
                    //resolve the plugin, as it is built into that paths layer.
                    if (bundleId) {
                        this.map.url = context.nameToUrl(bundleId);
                        this.load();
                        return;
                    }

                    load = bind(this, function (value) {
                        this.init([], function () { return value; }, null, {
                            enabled: true
                        });
                    });

                    load.error = bind(this, function (err) {
                        this.inited = true;
                        this.error = err;
                        err.requireModules = [id];

                        //Remove temp unnormalized modules for this module,
                        //since they will never be resolved otherwise now.
                        eachProp(registry, function (mod) {
                            if (mod.map.id.indexOf(id + '_unnormalized') === 0) {
                                cleanRegistry(mod.map.id);
                            }
                        });

                        onError(err);
                    });

                    //Allow plugins to load other code without having to know the
                    //context or how to 'complete' the load.
                    load.fromText = bind(this, function (text, textAlt) {
                        /*jslint evil: true */
                        var moduleName = map.name,
                            moduleMap = makeModuleMap(moduleName),
                            hasInteractive = useInteractive;

                        //As of 2.1.0, support just passing the text, to reinforce
                        //fromText only being called once per resource. Still
                        //support old style of passing moduleName but discard
                        //that moduleName in favor of the internal ref.
                        if (textAlt) {
                            text = textAlt;
                        }

                        //Turn off interactive script matching for IE for any define
                        //calls in the text, then turn it back on at the end.
                        if (hasInteractive) {
                            useInteractive = false;
                        }

                        //Prime the system by creating a module instance for
                        //it.
                        getModule(moduleMap);

                        //Transfer any config to this other module.
                        if (hasProp(config.config, id)) {
                            config.config[moduleName] = config.config[id];
                        }

                        try {
                            req.exec(text);
                        } catch (e) {
                            return onError(makeError('fromtexteval',
                                             'fromText eval for ' + id +
                                            ' failed: ' + e,
                                             e,
                                             [id]));
                        }

                        if (hasInteractive) {
                            useInteractive = true;
                        }

                        //Mark this as a dependency for the plugin
                        //resource
                        this.depMaps.push(moduleMap);

                        //Support anonymous modules.
                        context.completeLoad(moduleName);

                        //Bind the value of that module to the value for this
                        //resource ID.
                        localRequire([moduleName], load);
                    });

                    //Use parentName here since the plugin's name is not reliable,
                    //could be some weird string with no path that actually wants to
                    //reference the parentName's path.
                    plugin.load(map.name, localRequire, load, config);
                }));

                context.enable(pluginMap, this);
                this.pluginMaps[pluginMap.id] = pluginMap;
            },

            enable: function () {
                enabledRegistry[this.map.id] = this;
                this.enabled = true;

                //Set flag mentioning that the module is enabling,
                //so that immediate calls to the defined callbacks
                //for dependencies do not trigger inadvertent load
                //with the depCount still being zero.
                this.enabling = true;

                //Enable each dependency
                each(this.depMaps, bind(this, function (depMap, i) {
                    var id, mod, handler;

                    if (typeof depMap === 'string') {
                        //Dependency needs to be converted to a depMap
                        //and wired up to this module.
                        depMap = makeModuleMap(depMap,
                                               (this.map.isDefine ? this.map : this.map.parentMap),
                                               false,
                                               !this.skipMap);
                        this.depMaps[i] = depMap;

                        handler = getOwn(handlers, depMap.id);

                        if (handler) {
                            this.depExports[i] = handler(this);
                            return;
                        }

                        this.depCount += 1;

                        on(depMap, 'defined', bind(this, function (depExports) {
                            if (this.undefed) {
                                return;
                            }
                            this.defineDep(i, depExports);
                            this.check();
                        }));

                        if (this.errback) {
                            on(depMap, 'error', bind(this, this.errback));
                        } else if (this.events.error) {
                            // No direct errback on this module, but something
                            // else is listening for errors, so be sure to
                            // propagate the error correctly.
                            on(depMap, 'error', bind(this, function(err) {
                                this.emit('error', err);
                            }));
                        }
                    }

                    id = depMap.id;
                    mod = registry[id];

                    //Skip special modules like 'require', 'exports', 'module'
                    //Also, don't call enable if it is already enabled,
                    //important in circular dependency cases.
                    if (!hasProp(handlers, id) && mod && !mod.enabled) {
                        context.enable(depMap, this);
                    }
                }));

                //Enable each plugin that is used in
                //a dependency
                eachProp(this.pluginMaps, bind(this, function (pluginMap) {
                    var mod = getOwn(registry, pluginMap.id);
                    if (mod && !mod.enabled) {
                        context.enable(pluginMap, this);
                    }
                }));

                this.enabling = false;

                this.check();
            },

            on: function (name, cb) {
                var cbs = this.events[name];
                if (!cbs) {
                    cbs = this.events[name] = [];
                }
                cbs.push(cb);
            },

            emit: function (name, evt) {
                each(this.events[name], function (cb) {
                    cb(evt);
                });
                if (name === 'error') {
                    //Now that the error handler was triggered, remove
                    //the listeners, since this broken Module instance
                    //can stay around for a while in the registry.
                    delete this.events[name];
                }
            }
        };

        function callGetModule(args) {
            //Skip modules already defined.
            if (!hasProp(defined, args[0])) {
                getModule(makeModuleMap(args[0], null, true)).init(args[1], args[2]);
            }
        }

        function removeListener(node, func, name, ieName) {
            //Favor detachEvent because of IE9
            //issue, see attachEvent/addEventListener comment elsewhere
            //in this file.
            if (node.detachEvent && !isOpera) {
                //Probably IE. If not it will throw an error, which will be
                //useful to know.
                if (ieName) {
                    node.detachEvent(ieName, func);
                }
            } else {
                node.removeEventListener(name, func, false);
            }
        }

        /**
         * Given an event from a script node, get the requirejs info from it,
         * and then removes the event listeners on the node.
         * @param {Event} evt
         * @returns {Object}
         */
        function getScriptData(evt) {
            //Using currentTarget instead of target for Firefox 2.0's sake. Not
            //all old browsers will be supported, but this one was easy enough
            //to support and still makes sense.
            var node = evt.currentTarget || evt.srcElement;

            //Remove the listeners once here.
            removeListener(node, context.onScriptLoad, 'load', 'onreadystatechange');
            removeListener(node, context.onScriptError, 'error');

            return {
                node: node,
                id: node && node.getAttribute('data-requiremodule')
            };
        }

        function intakeDefines() {
            var args;

            //Any defined modules in the global queue, intake them now.
            takeGlobalQueue();

            //Make sure any remaining defQueue items get properly processed.
            while (defQueue.length) {
                args = defQueue.shift();
                if (args[0] === null) {
                    return onError(makeError('mismatch', 'Mismatched anonymous define() module: ' +
                        args[args.length - 1]));
                } else {
                    //args are id, deps, factory. Should be normalized by the
                    //define() function.
                    callGetModule(args);
                }
            }
            context.defQueueMap = {};
        }

        context = {
            config: config,
            contextName: contextName,
            registry: registry,
            defined: defined,
            urlFetched: urlFetched,
            defQueue: defQueue,
            defQueueMap: {},
            Module: Module,
            makeModuleMap: makeModuleMap,
            nextTick: req.nextTick,
            onError: onError,

            /**
             * Set a configuration for the context.
             * @param {Object} cfg config object to integrate.
             */
            configure: function (cfg) {
                //Make sure the baseUrl ends in a slash.
                if (cfg.baseUrl) {
                    if (cfg.baseUrl.charAt(cfg.baseUrl.length - 1) !== '/') {
                        cfg.baseUrl += '/';
                    }
                }

                //Save off the paths since they require special processing,
                //they are additive.
                var shim = config.shim,
                    objs = {
                        paths: true,
                        bundles: true,
                        config: true,
                        map: true
                    };

                eachProp(cfg, function (value, prop) {
                    if (objs[prop]) {
                        if (!config[prop]) {
                            config[prop] = {};
                        }
                        mixin(config[prop], value, true, true);
                    } else {
                        config[prop] = value;
                    }
                });

                //Reverse map the bundles
                if (cfg.bundles) {
                    eachProp(cfg.bundles, function (value, prop) {
                        each(value, function (v) {
                            if (v !== prop) {
                                bundlesMap[v] = prop;
                            }
                        });
                    });
                }

                //Merge shim
                if (cfg.shim) {
                    eachProp(cfg.shim, function (value, id) {
                        //Normalize the structure
                        if (isArray(value)) {
                            value = {
                                deps: value
                            };
                        }
                        if ((value.exports || value.init) && !value.exportsFn) {
                            value.exportsFn = context.makeShimExports(value);
                        }
                        shim[id] = value;
                    });
                    config.shim = shim;
                }

                //Adjust packages if necessary.
                if (cfg.packages) {
                    each(cfg.packages, function (pkgObj) {
                        var location, name;

                        pkgObj = typeof pkgObj === 'string' ? {name: pkgObj} : pkgObj;

                        name = pkgObj.name;
                        location = pkgObj.location;
                        if (location) {
                            config.paths[name] = pkgObj.location;
                        }

                        //Save pointer to main module ID for pkg name.
                        //Remove leading dot in main, so main paths are normalized,
                        //and remove any trailing .js, since different package
                        //envs have different conventions: some use a module name,
                        //some use a file name.
                        config.pkgs[name] = pkgObj.name + '/' + (pkgObj.main || 'main')
                                     .replace(currDirRegExp, '')
                                     .replace(jsSuffixRegExp, '');
                    });
                }

                //If there are any "waiting to execute" modules in the registry,
                //update the maps for them, since their info, like URLs to load,
                //may have changed.
                eachProp(registry, function (mod, id) {
                    //If module already has init called, since it is too
                    //late to modify them, and ignore unnormalized ones
                    //since they are transient.
                    if (!mod.inited && !mod.map.unnormalized) {
                        mod.map = makeModuleMap(id, null, true);
                    }
                });

                //If a deps array or a config callback is specified, then call
                //require with those args. This is useful when require is defined as a
                //config object before require.js is loaded.
                if (cfg.deps || cfg.callback) {
                    context.require(cfg.deps || [], cfg.callback);
                }
            },

            makeShimExports: function (value) {
                function fn() {
                    var ret;
                    if (value.init) {
                        ret = value.init.apply(global, arguments);
                    }
                    return ret || (value.exports && getGlobal(value.exports));
                }
                return fn;
            },

            makeRequire: function (relMap, options) {
                options = options || {};

                function localRequire(deps, callback, errback) {
                    var id, map, requireMod;

                    if (options.enableBuildCallback && callback && isFunction(callback)) {
                        callback.__requireJsBuild = true;
                    }

                    if (typeof deps === 'string') {
                        if (isFunction(callback)) {
                            //Invalid call
                            return onError(makeError('requireargs', 'Invalid require call'), errback);
                        }

                        //If require|exports|module are requested, get the
                        //value for them from the special handlers. Caveat:
                        //this only works while module is being defined.
                        if (relMap && hasProp(handlers, deps)) {
                            return handlers[deps](registry[relMap.id]);
                        }

                        //Synchronous access to one module. If require.get is
                        //available (as in the Node adapter), prefer that.
                        if (req.get) {
                            return req.get(context, deps, relMap, localRequire);
                        }

                        //Normalize module name, if it contains . or ..
                        map = makeModuleMap(deps, relMap, false, true);
                        id = map.id;

                        if (!hasProp(defined, id)) {
                            return onError(makeError('notloaded', 'Module name "' +
                                        id +
                                        '" has not been loaded yet for context: ' +
                                        contextName +
                                        (relMap ? '' : '. Use require([])')));
                        }
                        return defined[id];
                    }

                    //Grab defines waiting in the global queue.
                    intakeDefines();

                    //Mark all the dependencies as needing to be loaded.
                    context.nextTick(function () {
                        //Some defines could have been added since the
                        //require call, collect them.
                        intakeDefines();

                        requireMod = getModule(makeModuleMap(null, relMap));

                        //Store if map config should be applied to this require
                        //call for dependencies.
                        requireMod.skipMap = options.skipMap;

                        requireMod.init(deps, callback, errback, {
                            enabled: true
                        });

                        checkLoaded();
                    });

                    return localRequire;
                }

                mixin(localRequire, {
                    isBrowser: isBrowser,

                    /**
                     * Converts a module name + .extension into an URL path.
                     * *Requires* the use of a module name. It does not support using
                     * plain URLs like nameToUrl.
                     */
                    toUrl: function (moduleNamePlusExt) {
                        var ext,
                            index = moduleNamePlusExt.lastIndexOf('.'),
                            segment = moduleNamePlusExt.split('/')[0],
                            isRelative = segment === '.' || segment === '..';

                        //Have a file extension alias, and it is not the
                        //dots from a relative path.
                        if (index !== -1 && (!isRelative || index > 1)) {
                            ext = moduleNamePlusExt.substring(index, moduleNamePlusExt.length);
                            moduleNamePlusExt = moduleNamePlusExt.substring(0, index);
                        }

                        return context.nameToUrl(normalize(moduleNamePlusExt,
                                                relMap && relMap.id, true), ext,  true);
                    },

                    defined: function (id) {
                        return hasProp(defined, makeModuleMap(id, relMap, false, true).id);
                    },

                    specified: function (id) {
                        id = makeModuleMap(id, relMap, false, true).id;
                        return hasProp(defined, id) || hasProp(registry, id);
                    }
                });

                //Only allow undef on top level require calls
                if (!relMap) {
                    localRequire.undef = function (id) {
                        //Bind any waiting define() calls to this context,
                        //fix for #408
                        takeGlobalQueue();

                        var map = makeModuleMap(id, relMap, true),
                            mod = getOwn(registry, id);

                        mod.undefed = true;
                        removeScript(id);

                        delete defined[id];
                        delete urlFetched[map.url];
                        delete undefEvents[id];

                        //Clean queued defines too. Go backwards
                        //in array so that the splices do not
                        //mess up the iteration.
                        eachReverse(defQueue, function(args, i) {
                            if (args[0] === id) {
                                defQueue.splice(i, 1);
                            }
                        });
                        delete context.defQueueMap[id];

                        if (mod) {
                            //Hold on to listeners in case the
                            //module will be attempted to be reloaded
                            //using a different config.
                            if (mod.events.defined) {
                                undefEvents[id] = mod.events;
                            }

                            cleanRegistry(id);
                        }
                    };
                }

                return localRequire;
            },

            /**
             * Called to enable a module if it is still in the registry
             * awaiting enablement. A second arg, parent, the parent module,
             * is passed in for context, when this method is overridden by
             * the optimizer. Not shown here to keep code compact.
             */
            enable: function (depMap) {
                var mod = getOwn(registry, depMap.id);
                if (mod) {
                    getModule(depMap).enable();
                }
            },

            /**
             * Internal method used by environment adapters to complete a load event.
             * A load event could be a script load or just a load pass from a synchronous
             * load call.
             * @param {String} moduleName the name of the module to potentially complete.
             */
            completeLoad: function (moduleName) {
                var found, args, mod,
                    shim = getOwn(config.shim, moduleName) || {},
                    shExports = shim.exports;

                takeGlobalQueue();

                while (defQueue.length) {
                    args = defQueue.shift();
                    if (args[0] === null) {
                        args[0] = moduleName;
                        //If already found an anonymous module and bound it
                        //to this name, then this is some other anon module
                        //waiting for its completeLoad to fire.
                        if (found) {
                            break;
                        }
                        found = true;
                    } else if (args[0] === moduleName) {
                        //Found matching define call for this script!
                        found = true;
                    }

                    callGetModule(args);
                }
                context.defQueueMap = {};

                //Do this after the cycle of callGetModule in case the result
                //of those calls/init calls changes the registry.
                mod = getOwn(registry, moduleName);

                if (!found && !hasProp(defined, moduleName) && mod && !mod.inited) {
                    if (config.enforceDefine && (!shExports || !getGlobal(shExports))) {
                        if (hasPathFallback(moduleName)) {
                            return;
                        } else {
                            return onError(makeError('nodefine',
                                             'No define call for ' + moduleName,
                                             null,
                                             [moduleName]));
                        }
                    } else {
                        //A script that does not call define(), so just simulate
                        //the call for it.
                        callGetModule([moduleName, (shim.deps || []), shim.exportsFn]);
                    }
                }

                checkLoaded();
            },

            /**
             * Converts a module name to a file path. Supports cases where
             * moduleName may actually be just an URL.
             * Note that it **does not** call normalize on the moduleName,
             * it is assumed to have already been normalized. This is an
             * internal API, not a public one. Use toUrl for the public API.
             */
            nameToUrl: function (moduleName, ext, skipExt) {
                var paths, syms, i, parentModule, url,
                    parentPath, bundleId,
                    pkgMain = getOwn(config.pkgs, moduleName);

                if (pkgMain) {
                    moduleName = pkgMain;
                }

                bundleId = getOwn(bundlesMap, moduleName);

                if (bundleId) {
                    return context.nameToUrl(bundleId, ext, skipExt);
                }

                //If a colon is in the URL, it indicates a protocol is used and it is just
                //an URL to a file, or if it starts with a slash, contains a query arg (i.e. ?)
                //or ends with .js, then assume the user meant to use an url and not a module id.
                //The slash is important for protocol-less URLs as well as full paths.
                if (req.jsExtRegExp.test(moduleName)) {
                    //Just a plain path, not module name lookup, so just return it.
                    //Add extension if it is included. This is a bit wonky, only non-.js things pass
                    //an extension, this method probably needs to be reworked.
                    url = moduleName + (ext || '');
                } else {
                    //A module that needs to be converted to a path.
                    paths = config.paths;

                    syms = moduleName.split('/');
                    //For each module name segment, see if there is a path
                    //registered for it. Start with most specific name
                    //and work up from it.
                    for (i = syms.length; i > 0; i -= 1) {
                        parentModule = syms.slice(0, i).join('/');

                        parentPath = getOwn(paths, parentModule);
                        if (parentPath) {
                            //If an array, it means there are a few choices,
                            //Choose the one that is desired
                            if (isArray(parentPath)) {
                                parentPath = parentPath[0];
                            }
                            syms.splice(0, i, parentPath);
                            break;
                        }
                    }

                    //Join the path parts together, then figure out if baseUrl is needed.
                    url = syms.join('/');
                    url += (ext || (/^data\:|\?/.test(url) || skipExt ? '' : '.js'));
                    url = (url.charAt(0) === '/' || url.match(/^[\w\+\.\-]+:/) ? '' : config.baseUrl) + url;
                }

                return config.urlArgs ? url +
                                        ((url.indexOf('?') === -1 ? '?' : '&') +
                                         config.urlArgs) : url;
            },

            //Delegates to req.load. Broken out as a separate function to
            //allow overriding in the optimizer.
            load: function (id, url) {
                req.load(context, id, url);
            },

            /**
             * Executes a module callback function. Broken out as a separate function
             * solely to allow the build system to sequence the files in the built
             * layer in the right sequence.
             *
             * @private
             */
            execCb: function (name, callback, args, exports) {
                return callback.apply(exports, args);
            },

            /**
             * callback for script loads, used to check status of loading.
             *
             * @param {Event} evt the event from the browser for the script
             * that was loaded.
             */
            onScriptLoad: function (evt) {
                //Using currentTarget instead of target for Firefox 2.0's sake. Not
                //all old browsers will be supported, but this one was easy enough
                //to support and still makes sense.
                if (evt.type === 'load' ||
                        (readyRegExp.test((evt.currentTarget || evt.srcElement).readyState))) {
                    //Reset interactive script so a script node is not held onto for
                    //to long.
                    interactiveScript = null;

                    //Pull out the name of the module and the context.
                    var data = getScriptData(evt);
                    context.completeLoad(data.id);
                }
            },

            /**
             * Callback for script errors.
             */
            onScriptError: function (evt) {
                var data = getScriptData(evt);
                if (!hasPathFallback(data.id)) {
                    var parents = [];
                    eachProp(registry, function(value, key) {
                        if (key.indexOf('_@r') !== 0) {
                            each(value.depMaps, function(depMap) {
                                if (depMap.id === data.id) {
                                    parents.push(key);
                                }
                                return true;
                            });
                        }
                    });
                    return onError(makeError('scripterror', 'Script error for "' + data.id +
                                             (parents.length ?
                                             '", needed by: ' + parents.join(', ') :
                                             '"'), evt, [data.id]));
                }
            }
        };

        context.require = context.makeRequire();
        return context;
    }

    /**
     * Main entry point.
     *
     * If the only argument to require is a string, then the module that
     * is represented by that string is fetched for the appropriate context.
     *
     * If the first argument is an array, then it will be treated as an array
     * of dependency string names to fetch. An optional function callback can
     * be specified to execute when all of those dependencies are available.
     *
     * Make a local req variable to help Caja compliance (it assumes things
     * on a require that are not standardized), and to give a short
     * name for minification/local scope use.
     */
    req = requirejs = function (deps, callback, errback, optional) {

        //Find the right context, use default
        var context, config,
            contextName = defContextName;

        // Determine if have config object in the call.
        if (!isArray(deps) && typeof deps !== 'string') {
            // deps is a config object
            config = deps;
            if (isArray(callback)) {
                // Adjust args if there are dependencies
                deps = callback;
                callback = errback;
                errback = optional;
            } else {
                deps = [];
            }
        }

        if (config && config.context) {
            contextName = config.context;
        }

        context = getOwn(contexts, contextName);
        if (!context) {
            context = contexts[contextName] = req.s.newContext(contextName);
        }

        if (config) {
            context.configure(config);
        }

        return context.require(deps, callback, errback);
    };

    /**
     * Support require.config() to make it easier to cooperate with other
     * AMD loaders on globally agreed names.
     */
    req.config = function (config) {
        return req(config);
    };

    /**
     * Execute something after the current tick
     * of the event loop. Override for other envs
     * that have a better solution than setTimeout.
     * @param  {Function} fn function to execute later.
     */
    req.nextTick = typeof setTimeout !== 'undefined' ? function (fn) {
        setTimeout(fn, 4);
    } : function (fn) { fn(); };

    /**
     * Export require as a global, but only if it does not already exist.
     */
    if (!require) {
        require = req;
    }

    req.version = version;

    //Used to filter out dependencies that are already paths.
    req.jsExtRegExp = /^\/|:|\?|\.js$/;
    req.isBrowser = isBrowser;
    s = req.s = {
        contexts: contexts,
        newContext: newContext
    };

    //Create default context.
    req({});

    //Exports some context-sensitive methods on global require.
    each([
        'toUrl',
        'undef',
        'defined',
        'specified'
    ], function (prop) {
        //Reference from contexts instead of early binding to default context,
        //so that during builds, the latest instance of the default context
        //with its config gets used.
        req[prop] = function () {
            var ctx = contexts[defContextName];
            return ctx.require[prop].apply(ctx, arguments);
        };
    });

    if (isBrowser) {
        head = s.head = document.getElementsByTagName('head')[0];
        //If BASE tag is in play, using appendChild is a problem for IE6.
        //When that browser dies, this can be removed. Details in this jQuery bug:
        //http://dev.jquery.com/ticket/2709
        baseElement = document.getElementsByTagName('base')[0];
        if (baseElement) {
            head = s.head = baseElement.parentNode;
        }
    }

    /**
     * Any errors that require explicitly generates will be passed to this
     * function. Intercept/override it if you want custom error handling.
     * @param {Error} err the error object.
     */
    req.onError = defaultOnError;

    /**
     * Creates the node for the load command. Only used in browser envs.
     */
    req.createNode = function (config, moduleName, url) {
        var node = config.xhtml ?
                document.createElementNS('http://www.w3.org/1999/xhtml', 'html:script') :
                document.createElement('script');
        node.type = config.scriptType || 'text/javascript';
        node.charset = 'utf-8';
        node.async = true;
        return node;
    };

    /**
     * Does the request to load a module for the browser case.
     * Make this a separate function to allow other environments
     * to override it.
     *
     * @param {Object} context the require context to find state.
     * @param {String} moduleName the name of the module.
     * @param {Object} url the URL to the module.
     */
    req.load = function (context, moduleName, url) {
        var config = (context && context.config) || {},
            node;
        if (isBrowser) {
            //In the browser so use a script tag
            node = req.createNode(config, moduleName, url);
            if (config.onNodeCreated) {
                config.onNodeCreated(node, config, moduleName, url);
            }

            node.setAttribute('data-requirecontext', context.contextName);
            node.setAttribute('data-requiremodule', moduleName);

            //Set up load listener. Test attachEvent first because IE9 has
            //a subtle issue in its addEventListener and script onload firings
            //that do not match the behavior of all other browsers with
            //addEventListener support, which fire the onload event for a
            //script right after the script execution. See:
            //https://connect.microsoft.com/IE/feedback/details/648057/script-onload-event-is-not-fired-immediately-after-script-execution
            //UNFORTUNATELY Opera implements attachEvent but does not follow the script
            //script execution mode.
            if (node.attachEvent &&
                    //Check if node.attachEvent is artificially added by custom script or
                    //natively supported by browser
                    //read https://github.com/jrburke/requirejs/issues/187
                    //if we can NOT find [native code] then it must NOT natively supported.
                    //in IE8, node.attachEvent does not have toString()
                    //Note the test for "[native code" with no closing brace, see:
                    //https://github.com/jrburke/requirejs/issues/273
                    !(node.attachEvent.toString && node.attachEvent.toString().indexOf('[native code') < 0) &&
                    !isOpera) {
                //Probably IE. IE (at least 6-8) do not fire
                //script onload right after executing the script, so
                //we cannot tie the anonymous define call to a name.
                //However, IE reports the script as being in 'interactive'
                //readyState at the time of the define call.
                useInteractive = true;

                node.attachEvent('onreadystatechange', context.onScriptLoad);
                //It would be great to add an error handler here to catch
                //404s in IE9+. However, onreadystatechange will fire before
                //the error handler, so that does not help. If addEventListener
                //is used, then IE will fire error before load, but we cannot
                //use that pathway given the connect.microsoft.com issue
                //mentioned above about not doing the 'script execute,
                //then fire the script load event listener before execute
                //next script' that other browsers do.
                //Best hope: IE10 fixes the issues,
                //and then destroys all installs of IE 6-9.
                //node.attachEvent('onerror', context.onScriptError);
            } else {
                node.addEventListener('load', context.onScriptLoad, false);
                node.addEventListener('error', context.onScriptError, false);
            }
            node.src = url;

            //For some cache cases in IE 6-8, the script executes before the end
            //of the appendChild execution, so to tie an anonymous define
            //call to the module name (which is stored on the node), hold on
            //to a reference to this node, but clear after the DOM insertion.
            currentlyAddingScript = node;
            if (baseElement) {
                head.insertBefore(node, baseElement);
            } else {
                head.appendChild(node);
            }
            currentlyAddingScript = null;

            return node;
        } else if (isWebWorker) {
            try {
                //In a web worker, use importScripts. This is not a very
                //efficient use of importScripts, importScripts will block until
                //its script is downloaded and evaluated. However, if web workers
                //are in play, the expectation is that a build has been done so
                //that only one script needs to be loaded anyway. This may need
                //to be reevaluated if other use cases become common.
                importScripts(url);

                //Account for anonymous modules
                context.completeLoad(moduleName);
            } catch (e) {
                context.onError(makeError('importscripts',
                                'importScripts failed for ' +
                                    moduleName + ' at ' + url,
                                e,
                                [moduleName]));
            }
        }
    };

    function getInteractiveScript() {
        if (interactiveScript && interactiveScript.readyState === 'interactive') {
            return interactiveScript;
        }

        eachReverse(scripts(), function (script) {
            if (script.readyState === 'interactive') {
                return (interactiveScript = script);
            }
        });
        return interactiveScript;
    }

    //Look for a data-main script attribute, which could also adjust the baseUrl.
    if (isBrowser && !cfg.skipDataMain) {
        //Figure out baseUrl. Get it from the script tag with require.js in it.
        eachReverse(scripts(), function (script) {
            //Set the 'head' where we can append children by
            //using the script's parent.
            if (!head) {
                head = script.parentNode;
            }

            //Look for a data-main attribute to set main script for the page
            //to load. If it is there, the path to data main becomes the
            //baseUrl, if it is not already set.
            dataMain = script.getAttribute('data-main');
            if (dataMain) {
                //Preserve dataMain in case it is a path (i.e. contains '?')
                mainScript = dataMain;

                //Set final baseUrl if there is not already an explicit one.
                if (!cfg.baseUrl) {
                    //Pull off the directory of data-main for use as the
                    //baseUrl.
                    src = mainScript.split('/');
                    mainScript = src.pop();
                    subPath = src.length ? src.join('/')  + '/' : './';

                    cfg.baseUrl = subPath;
                }

                //Strip off any trailing .js since mainScript is now
                //like a module name.
                mainScript = mainScript.replace(jsSuffixRegExp, '');

                //If mainScript is still a path, fall back to dataMain
                if (req.jsExtRegExp.test(mainScript)) {
                    mainScript = dataMain;
                }

                //Put the data-main script in the files to load.
                cfg.deps = cfg.deps ? cfg.deps.concat(mainScript) : [mainScript];

                return true;
            }
        });
    }

    /**
     * The function that handles definitions of modules. Differs from
     * require() in that a string for the module should be the first argument,
     * and the function to execute after dependencies are loaded should
     * return a value to define the module corresponding to the first argument's
     * name.
     */
    define = function (name, deps, callback) {
        var node, context;

        //Allow for anonymous modules
        if (typeof name !== 'string') {
            //Adjust args appropriately
            callback = deps;
            deps = name;
            name = null;
        }

        //This module may not have dependencies
        if (!isArray(deps)) {
            callback = deps;
            deps = null;
        }

        //If no name, and callback is a function, then figure out if it a
        //CommonJS thing with dependencies.
        if (!deps && isFunction(callback)) {
            deps = [];
            //Remove comments from the callback string,
            //look for require calls, and pull them into the dependencies,
            //but only if there are function args.
            if (callback.length) {
                callback
                    .toString()
                    .replace(commentRegExp, '')
                    .replace(cjsRequireRegExp, function (match, dep) {
                        deps.push(dep);
                    });

                //May be a CommonJS thing even without require calls, but still
                //could use exports, and module. Avoid doing exports and module
                //work though if it just needs require.
                //REQUIRES the function to expect the CommonJS variables in the
                //order listed below.
                deps = (callback.length === 1 ? ['require'] : ['require', 'exports', 'module']).concat(deps);
            }
        }

        //If in IE 6-8 and hit an anonymous define() call, do the interactive
        //work.
        if (useInteractive) {
            node = currentlyAddingScript || getInteractiveScript();
            if (node) {
                if (!name) {
                    name = node.getAttribute('data-requiremodule');
                }
                context = contexts[node.getAttribute('data-requirecontext')];
            }
        }

        //Always save off evaluating the def call until the script onload handler.
        //This allows multiple modules to be in a file without prematurely
        //tracing dependencies, and allows for anonymous module support,
        //where the module name is not known until the script onload event
        //occurs. If no context, use the global queue, and get it processed
        //in the onscript load callback.
        if (context) {
            context.defQueue.push([name, deps, callback]);
            context.defQueueMap[name] = true;
        } else {
            globalDefQueue.push([name, deps, callback]);
        }
    };

    define.amd = {
        jQuery: true
    };

    /**
     * Executes the text. Normally just uses eval, but can be modified
     * to use a better, environment-specific call. Only used for transpiling
     * loader plugins, not for plain JS modules.
     * @param {String} text the text to execute/evaluate.
     */
    req.exec = function (text) {
        /*jslint evil: true */
        return eval(text);
    };

    //Set up with config info.
    req(cfg);
}(this));

define("../lib/requirejs/require", function(){});

(function() {
    var root;

	if (typeof window === 'object' && window) {
		root = window;
	} else {
		root = global;
	}

	if (typeof module !== 'undefined' && module.exports) {
		module.exports = root.Promise ? root.Promise : Promise;
	} else if (!root.Promise) {
		root.Promise = Promise;
	}

	// Use polyfill for setImmediate for performance gains
	var asap = root.setImmediate || function(fn) { setTimeout(fn, 1); };

	// Polyfill for Function.prototype.bind
	function bind(fn, thisArg) {
		return function() {
			fn.apply(thisArg, arguments);
		}
	}

	var isArray = Array.isArray || function(value) { return Object.prototype.toString.call(value) === "[object Array]" };

	function Promise(fn) {
		if (typeof this !== 'object') throw new TypeError('Promises must be constructed via new');
		if (typeof fn !== 'function') throw new TypeError('not a function');
		this._state = null;
		this._value = null;
		this._deferreds = []

		doResolve(fn, bind(resolve, this), bind(reject, this))
	}

	function handle(deferred) {
		var me = this;
		if (this._state === null) {
			this._deferreds.push(deferred);
			return
		}
		asap(function() {
			var cb = me._state ? deferred.onFulfilled : deferred.onRejected
			if (cb === null) {
				(me._state ? deferred.resolve : deferred.reject)(me._value);
				return;
			}
			var ret;
			try {
				ret = cb(me._value);
			}
			catch (e) {
				deferred.reject(e);
				return;
			}
			deferred.resolve(ret);
		})
	}

	function resolve(newValue) {
		try { //Promise Resolution Procedure: https://github.com/promises-aplus/promises-spec#the-promise-resolution-procedure
			if (newValue === this) throw new TypeError('A promise cannot be resolved with itself.');
			if (newValue && (typeof newValue === 'object' || typeof newValue === 'function')) {
				var then = newValue.then;
				if (typeof then === 'function') {
					doResolve(bind(then, newValue), bind(resolve, this), bind(reject, this));
					return;
				}
			}
			this._state = true;
			this._value = newValue;
			finale.call(this);
		} catch (e) { reject.call(this, e); }
	}

	function reject(newValue) {
		this._state = false;
		this._value = newValue;
		finale.call(this);
	}

	function finale() {
		for (var i = 0, len = this._deferreds.length; i < len; i++) {
			handle.call(this, this._deferreds[i]);
		}
		this._deferreds = null;
	}

	function Handler(onFulfilled, onRejected, resolve, reject){
		this.onFulfilled = typeof onFulfilled === 'function' ? onFulfilled : null;
		this.onRejected = typeof onRejected === 'function' ? onRejected : null;
		this.resolve = resolve;
		this.reject = reject;
	}

	/**
	 * Take a potentially misbehaving resolver function and make sure
	 * onFulfilled and onRejected are only called once.
	 *
	 * Makes no guarantees about asynchrony.
	 */
	function doResolve(fn, onFulfilled, onRejected) {
		var done = false;
		try {
			fn(function (value) {
				if (done) return;
				done = true;
				onFulfilled(value);
			}, function (reason) {
				if (done) return;
				done = true;
				onRejected(reason);
			})
		} catch (ex) {
			if (done) return;
			done = true;
			onRejected(ex);
		}
	}

	Promise.prototype['catch'] = function (onRejected) {
		return this.then(null, onRejected);
	};

	Promise.prototype.then = function(onFulfilled, onRejected) {
		var me = this;
		return new Promise(function(resolve, reject) {
			handle.call(me, new Handler(onFulfilled, onRejected, resolve, reject));
		})
	};

	Promise.all = function () {
		var args = Array.prototype.slice.call(arguments.length === 1 && isArray(arguments[0]) ? arguments[0] : arguments);

		return new Promise(function (resolve, reject) {
			if (args.length === 0) return resolve([]);
			var remaining = args.length;
			function res(i, val) {
				try {
					if (val && (typeof val === 'object' || typeof val === 'function')) {
						var then = val.then;
						if (typeof then === 'function') {
							then.call(val, function (val) { res(i, val) }, reject);
							return;
						}
					}
					args[i] = val;
					if (--remaining === 0) {
						resolve(args);
					}
				} catch (ex) {
					reject(ex);
				}
			}
			for (var i = 0; i < args.length; i++) {
				res(i, args[i]);
			}
		});
	};

	Promise.resolve = function (value) {
		if (value && typeof value === 'object' && value.constructor === Promise) {
			return value;
		}

		return new Promise(function (resolve) {
			resolve(value);
		});
	};

	Promise.reject = function (value) {
		return new Promise(function (resolve, reject) {
			reject(value);
		});
	};

	Promise.race = function (values) {
		return new Promise(function (resolve, reject) {
			for(var i = 0, len = values.length; i < len; i++) {
				values[i].then(resolve, reject);
			}
		});
	};
})();
define("promise", (function (global) {
    return function () {
        var ret, fn;
        return ret || global.Promise;
    };
}(this)));

require.config({
	'baseUrl': './',
	'paths': {
		'text':                     '../lib/requirejs-text/text',

		'app': 'app',

		// 3rd party
		'markdown':'../lib/markdown/lib/markdown',
		'gyro':'../lib/gyro.js/js/gyro',
		'promise':'../lib/promise-polyfill/Promise', // Fuck you IE
		'object-store':'../lib/object-store/ObjectStore',
		'superagent':                 '../lib/superagent/superagent',
		'base64':                 '../lib/js-base64/base64',
		'tiny-emitter':                 '../lib/tiny-emitter/dist/tinyemitter',

		// 'facebook': '//connect.facebook.net/en_US/all'
		'youtubePlayer': '//www.youtube.com/player_api'
	},
	'packages': [

		{ name: 'core',                     location: 'packages/core/src'},
		{ name: 'input-manager',            location: 'packages/input-manager/src'},
		{ name: 'output-manager',           location: 'packages/output-manager/src'},
		{ name: 'command-manager',          location: 'packages/command-manager/src'},
		{ name: 'window-manager',           location: 'packages/window-manager/src'},
		{ name: 'request-manager',          location: 'packages/request-manager/src'},
		{ name: 'sensor-manager',           location: 'packages/sensor-manager/src'},
		{ name: 'portfolio-manager',        location: 'packages/portfolio-manager/src'},

		{ name: 'controllers',              location: 'packages/controllers/src'},
		{ name: 'canvases',                 location: 'packages/canvases/src'},
		{ name: 'panvas',                   location: 'packages/panvas/src'},

		// 3rd party
		{ name: 'minimist',                 location: 'packages/minimist/src'},

		//{ name: 'portfolio',                location: 'http://portfolio'}
		{ name: 'portfolio',                location: 'packages/portfolio/src'}
	],

	shim: {
		promise: {
			exports: 'Promise'
		},
		markdown: {
			exports: 'markdown'
		},
		facebook : {
			exports: 'FB'
		},
		base64 : {
			exports: 'Base64'
		}
	}
});

// Make sure to load all the polyfills first, only after they are loaded, start the main application
require([
	'promise'
], function() {
});

define("bootstrap", function(){});

/*
 * $Id: base64.js,v 2.15 2014/04/05 12:58:57 dankogai Exp dankogai $
 *
 *  Licensed under the MIT license.
 *    http://opensource.org/licenses/mit-license
 *
 *  References:
 *    http://en.wikipedia.org/wiki/Base64
 */

(function(global) {
    'use strict';
    // existing version for noConflict()
    var _Base64 = global.Base64;
    var version = "2.1.9";
    // if node.js, we use Buffer
    var buffer;
    if (typeof module !== 'undefined' && module.exports) {
        try {
            buffer = require('buffer').Buffer;
        } catch (err) {}
    }
    // constants
    var b64chars
        = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/';
    var b64tab = function(bin) {
        var t = {};
        for (var i = 0, l = bin.length; i < l; i++) t[bin.charAt(i)] = i;
        return t;
    }(b64chars);
    var fromCharCode = String.fromCharCode;
    // encoder stuff
    var cb_utob = function(c) {
        if (c.length < 2) {
            var cc = c.charCodeAt(0);
            return cc < 0x80 ? c
                : cc < 0x800 ? (fromCharCode(0xc0 | (cc >>> 6))
                                + fromCharCode(0x80 | (cc & 0x3f)))
                : (fromCharCode(0xe0 | ((cc >>> 12) & 0x0f))
                   + fromCharCode(0x80 | ((cc >>>  6) & 0x3f))
                   + fromCharCode(0x80 | ( cc         & 0x3f)));
        } else {
            var cc = 0x10000
                + (c.charCodeAt(0) - 0xD800) * 0x400
                + (c.charCodeAt(1) - 0xDC00);
            return (fromCharCode(0xf0 | ((cc >>> 18) & 0x07))
                    + fromCharCode(0x80 | ((cc >>> 12) & 0x3f))
                    + fromCharCode(0x80 | ((cc >>>  6) & 0x3f))
                    + fromCharCode(0x80 | ( cc         & 0x3f)));
        }
    };
    var re_utob = /[\uD800-\uDBFF][\uDC00-\uDFFFF]|[^\x00-\x7F]/g;
    var utob = function(u) {
        return u.replace(re_utob, cb_utob);
    };
    var cb_encode = function(ccc) {
        var padlen = [0, 2, 1][ccc.length % 3],
        ord = ccc.charCodeAt(0) << 16
            | ((ccc.length > 1 ? ccc.charCodeAt(1) : 0) << 8)
            | ((ccc.length > 2 ? ccc.charCodeAt(2) : 0)),
        chars = [
            b64chars.charAt( ord >>> 18),
            b64chars.charAt((ord >>> 12) & 63),
            padlen >= 2 ? '=' : b64chars.charAt((ord >>> 6) & 63),
            padlen >= 1 ? '=' : b64chars.charAt(ord & 63)
        ];
        return chars.join('');
    };
    var btoa = global.btoa ? function(b) {
        return global.btoa(b);
    } : function(b) {
        return b.replace(/[\s\S]{1,3}/g, cb_encode);
    };
    var _encode = buffer ? function (u) {
        return (u.constructor === buffer.constructor ? u : new buffer(u))
        .toString('base64')
    }
    : function (u) { return btoa(utob(u)) }
    ;
    var encode = function(u, urisafe) {
        return !urisafe
            ? _encode(String(u))
            : _encode(String(u)).replace(/[+\/]/g, function(m0) {
                return m0 == '+' ? '-' : '_';
            }).replace(/=/g, '');
    };
    var encodeURI = function(u) { return encode(u, true) };
    // decoder stuff
    var re_btou = new RegExp([
        '[\xC0-\xDF][\x80-\xBF]',
        '[\xE0-\xEF][\x80-\xBF]{2}',
        '[\xF0-\xF7][\x80-\xBF]{3}'
    ].join('|'), 'g');
    var cb_btou = function(cccc) {
        switch(cccc.length) {
        case 4:
            var cp = ((0x07 & cccc.charCodeAt(0)) << 18)
                |    ((0x3f & cccc.charCodeAt(1)) << 12)
                |    ((0x3f & cccc.charCodeAt(2)) <<  6)
                |     (0x3f & cccc.charCodeAt(3)),
            offset = cp - 0x10000;
            return (fromCharCode((offset  >>> 10) + 0xD800)
                    + fromCharCode((offset & 0x3FF) + 0xDC00));
        case 3:
            return fromCharCode(
                ((0x0f & cccc.charCodeAt(0)) << 12)
                    | ((0x3f & cccc.charCodeAt(1)) << 6)
                    |  (0x3f & cccc.charCodeAt(2))
            );
        default:
            return  fromCharCode(
                ((0x1f & cccc.charCodeAt(0)) << 6)
                    |  (0x3f & cccc.charCodeAt(1))
            );
        }
    };
    var btou = function(b) {
        return b.replace(re_btou, cb_btou);
    };
    var cb_decode = function(cccc) {
        var len = cccc.length,
        padlen = len % 4,
        n = (len > 0 ? b64tab[cccc.charAt(0)] << 18 : 0)
            | (len > 1 ? b64tab[cccc.charAt(1)] << 12 : 0)
            | (len > 2 ? b64tab[cccc.charAt(2)] <<  6 : 0)
            | (len > 3 ? b64tab[cccc.charAt(3)]       : 0),
        chars = [
            fromCharCode( n >>> 16),
            fromCharCode((n >>>  8) & 0xff),
            fromCharCode( n         & 0xff)
        ];
        chars.length -= [0, 0, 2, 1][padlen];
        return chars.join('');
    };
    var atob = global.atob ? function(a) {
        return global.atob(a);
    } : function(a){
        return a.replace(/[\s\S]{1,4}/g, cb_decode);
    };
    var _decode = buffer ? function(a) {
        return (a.constructor === buffer.constructor
                ? a : new buffer(a, 'base64')).toString();
    }
    : function(a) { return btou(atob(a)) };
    var decode = function(a){
        return _decode(
            String(a).replace(/[-_]/g, function(m0) { return m0 == '-' ? '+' : '/' })
                .replace(/[^A-Za-z0-9\+\/]/g, '')
        );
    };
    var noConflict = function() {
        var Base64 = global.Base64;
        global.Base64 = _Base64;
        return Base64;
    };
    // export Base64
    global.Base64 = {
        VERSION: version,
        atob: atob,
        btoa: btoa,
        fromBase64: decode,
        toBase64: encode,
        utob: utob,
        encode: encode,
        encodeURI: encodeURI,
        btou: btou,
        decode: decode,
        noConflict: noConflict
    };
    // if ES5 is available, make Base64.extendString() available
    if (typeof Object.defineProperty === 'function') {
        var noEnum = function(v){
            return {value:v,enumerable:false,writable:true,configurable:true};
        };
        global.Base64.extendString = function () {
            Object.defineProperty(
                String.prototype, 'fromBase64', noEnum(function () {
                    return decode(this)
                }));
            Object.defineProperty(
                String.prototype, 'toBase64', noEnum(function (urisafe) {
                    return encode(this, urisafe)
                }));
            Object.defineProperty(
                String.prototype, 'toBase64URI', noEnum(function () {
                    return encode(this, true)
                }));
        };
    }
    // that's it!
    if (global['Meteor']) {
       Base64 = global.Base64; // for normal export in Meteor.js
    }
})(this);

define("base64", (function (global) {
    return function () {
        var ret, fn;
        return ret || global.Base64;
    };
}(this)));

define('minimist/main',[
], function (
) {

	// Adaption of:
	// https://raw.githubusercontent.com/substack/minimist/e2563e462be40c344c6c65b7cde85091fe261976/index.js

	function minimist(args, opts) {
		if (!opts) opts = {};

		var flags = { bools : {}, strings : {}, unknownFn: null };

		if (typeof opts['unknown'] === 'function') {
			flags.unknownFn = opts['unknown'];
		}

		if (typeof opts['boolean'] === 'boolean' && opts['boolean']) {
			flags.allBools = true;
		} else {
			[].concat(opts['boolean']).filter(Boolean).forEach(function (key) {
				flags.bools[key] = true;
			});
		}

		var aliases = {};
		Object.keys(opts.alias || {}).forEach(function (key) {
			aliases[key] = [].concat(opts.alias[key]);
			aliases[key].forEach(function (x) {
				aliases[x] = [key].concat(aliases[key].filter(function (y) {
					return x !== y;
				}));
			});
		});

		[].concat(opts.string).filter(Boolean).forEach(function (key) {
			flags.strings[key] = true;
			if (aliases[key]) {
				flags.strings[aliases[key]] = true;
			}
		});

		var defaults = opts['default'] || {};

		var argv = { _ : [] };
		Object.keys(flags.bools).forEach(function (key) {
			setArg(key, defaults[key] === undefined ? false : defaults[key]);
		});

		var notFlags = [];

		if (args.indexOf('--') !== -1) {
			notFlags = args.slice(args.indexOf('--')+1);
			args = args.slice(0, args.indexOf('--'));
		}

		function argDefined(key, arg) {
			return (flags.allBools && /^--[^=]+$/.test(arg)) ||
				flags.strings[key] || flags.bools[key] || aliases[key];
		}

		function setArg (key, val, arg) {
			if (arg && flags.unknownFn && !argDefined(key, arg)) {
				if (flags.unknownFn(arg) === false) return;
			}

			var value = !flags.strings[key] && isNumber(val)
					? Number(val) : val
				;
			setKey(argv, key.split('.'), value);

			(aliases[key] || []).forEach(function (x) {
				setKey(argv, x.split('.'), value);
			});
		}

		for (var i = 0; i < args.length; i++) {
			var arg = args[i];

			if (/^--.+=/.test(arg)) {
				// Using [\s\S] instead of . because js doesn't support the
				// 'dotall' regex modifier. See:
				// http://stackoverflow.com/a/1068308/13216
				var m = arg.match(/^--([^=]+)=([\s\S]*)$/);
				setArg(m[1], m[2], arg);
			}
			else if (/^--no-.+/.test(arg)) {
				var key = arg.match(/^--no-(.+)/)[1];
				setArg(key, false, arg);
			}
			else if (/^--.+/.test(arg)) {
				var key = arg.match(/^--(.+)/)[1];
				var next = args[i + 1];
				if (next !== undefined && !/^-/.test(next)
					&& !flags.bools[key]
					&& !flags.allBools
					&& (aliases[key] ? !flags.bools[aliases[key]] : true)) {
					setArg(key, next, arg);
					i++;
				}
				else if (/^(true|false)$/.test(next)) {
					setArg(key, next === 'true', arg);
					i++;
				}
				else {
					setArg(key, flags.strings[key] ? '' : true, arg);
				}
			}
			else if (/^-[^-]+/.test(arg)) {
				var letters = arg.slice(1,-1).split('');

				var broken = false;
				for (var j = 0; j < letters.length; j++) {
					var next = arg.slice(j+2);

					if (next === '-') {
						setArg(letters[j], next, arg)
						continue;
					}

					if (/[A-Za-z]/.test(letters[j])
						&& /-?\d+(\.\d*)?(e-?\d+)?$/.test(next)) {
						setArg(letters[j], next, arg);
						broken = true;
						break;
					}

					if (letters[j+1] && letters[j+1].match(/\W/)) {
						setArg(letters[j], arg.slice(j+2), arg);
						broken = true;
						break;
					}
					else {
						setArg(letters[j], flags.strings[letters[j]] ? '' : true, arg);
					}
				}

				var key = arg.slice(-1)[0];
				if (!broken && key !== '-') {
					if (args[i+1] && !/^(-|--)[^-]/.test(args[i+1])
						&& !flags.bools[key]
						&& (aliases[key] ? !flags.bools[aliases[key]] : true)) {
						setArg(key, args[i+1], arg);
						i++;
					}
					else if (args[i+1] && /true|false/.test(args[i+1])) {
						setArg(key, args[i+1] === 'true', arg);
						i++;
					}
					else {
						setArg(key, flags.strings[key] ? '' : true, arg);
					}
				}
			}
			else {
				if (!flags.unknownFn || flags.unknownFn(arg) !== false) {
					argv._.push(
							flags.strings['_'] || !isNumber(arg) ? arg : Number(arg)
					);
				}
				if (opts.stopEarly) {
					argv._.push.apply(argv._, args.slice(i + 1));
					break;
				}
			}
		}

		Object.keys(defaults).forEach(function (key) {
			if (!hasKey(argv, key.split('.'))) {
				setKey(argv, key.split('.'), defaults[key]);

				(aliases[key] || []).forEach(function (x) {
					setKey(argv, x.split('.'), defaults[key]);
				});
			}
		});

		if (opts['--']) {
			argv['--'] = new Array();
			notFlags.forEach(function(key) {
				argv['--'].push(key);
			});
		}
		else {
			notFlags.forEach(function(key) {
				argv._.push(key);
			});
		}

		return argv;
	}

	function hasKey (obj, keys) {
		var o = obj;
		keys.slice(0,-1).forEach(function (key) {
			o = (o[key] || {});
		});

		var key = keys[keys.length - 1];
		return key in o;
	}

	function setKey (obj, keys, value) {
		var o = obj;
		keys.slice(0,-1).forEach(function (key) {
			if (o[key] === undefined) o[key] = {};
			o = o[key];
		});

		var key = keys[keys.length - 1];
		if (o[key] === undefined || typeof o[key] === 'boolean') {
			o[key] = value;
		}
		else if (Array.isArray(o[key])) {
			o[key].push(value);
		}
		else {
			o[key] = [ o[key], value ];
		}
	}

	function isNumber (x) {
		if (typeof x === 'number') return true;
		if (/^0x[0-9a-f]+$/i.test(x)) return true;
		return /^[-+]?(?:\d+(?:\.\d*)?|\.\d+)(e[-+]?\d+)?$/.test(x);
	}

	return minimist;
});
define('minimist', ['minimist/main'], function (main) { return main; });

define('input-manager/Request',[
	'minimist'
], function (
	minimist
) {

	function Request (value) {
		if(typeof value !== 'string')
			throw new Error('Invalid argument for new Request, must be a string');

		var minimized = minimist((value || '').split(' ')),
			route = [],
			options = {};

		Object.keys(minimized).forEach(function(key) {
			if(key === '_')
				route = minimized[key].map(function(val) {
					return (''+val).trim();
				});
			else
				options[key] = minimized[key];
		});

		this.input = value;
		this.route = route;
		this.options = options;
	}

	return Request;
});
define('input-manager/InputCursor',[
	'minimist'
], function (
	minimist
) {

	var CSS_CLASS = 'input__overlay__cursor';

	function InputCursor () {
		this.element = this.createElement();
		this.start();
	}


	InputCursor.prototype.createElement = function() {
		var inputCursor = document.createElement('span');
		inputCursor.classList.add(CSS_CLASS);

		return inputCursor;
	};

	InputCursor.prototype.start = function() {
		this.blink()
	};
	InputCursor.prototype.stop = function() {
		this.hide();
	};

	InputCursor.prototype.blink = function() {
		this.element.classList.remove(CSS_CLASS + '--pinned');
		this.element.classList.remove(CSS_CLASS + '--hidden');
		this.element.classList.add(CSS_CLASS + '--blinking');
	};
	InputCursor.prototype.pin = function() {
		this.element.classList.add(CSS_CLASS + '--pinned');
		this.element.classList.remove(CSS_CLASS + '--hidden');
		this.element.classList.remove(CSS_CLASS + '--blinking');
	};
	InputCursor.prototype.hide = function() {
		this.element.classList.remove(CSS_CLASS + '--pinned');
		this.element.classList.add(CSS_CLASS + '--hidden');
		this.element.classList.remove(CSS_CLASS + '--blinking');
	};

	return InputCursor;
});
define('input-manager/InputSuggestions',[], function () {
	function InputSuggestions () {
		this.element = this.createElement();
	}

	InputSuggestions.prototype.createElement = function() {
		var el = document.createElement('span');
		el.classList.add('input__overlay__suggestions');
		return el;
	};

	InputSuggestions.prototype.populateFromCommands = function(commands) {
		if(!this.element)
			this.element = this.createElement();

		this.element.innerHTML = '';
		commands.forEach(function(command, i) {
			var aElement = document.createElement('a');
			aElement.setAttribute('command', command.getRoute().slice(1).join(' '));
			aElement.appendChild(document.createTextNode(command.name));
			aElement.classList.add('input__overlay__suggestion');

			this.element.appendChild(aElement);

			if(i < commands.length - 1)
				this.element.appendChild(document.createTextNode('/'));
		}.bind(this));
	};

	return InputSuggestions;
});
define('input-manager/InputHistory',[], function () {

	function InputHistory (submitCallback) {
		this.submitted = [];
		this.pointer = 0;
		this.submitCallback = submitCallback;
	}

	InputHistory.prototype.onwardIfNotAtPointer = function (value) {
		if(this.submitted[this.pointer] && value.input === this.submitted[this.pointer].input)
			return;

		this.onward(value);
	};

	// Clears all history items newer than pointer, and creates new entry
	InputHistory.prototype.onward = function(value) {
		if(this.pointer) {
			this.submitted.splice(0, this.pointer);
		}

		this.submitted.unshift(value);

		this.pointer = 0;
	};


	InputHistory.prototype.getBackward = function() {
		if(this.pointer >= this.submitted.length - 1)
			throw new Error('Already at oldest record');

		++this.pointer;

		return this.submitted[this.pointer];
	};

	InputHistory.prototype.getForward = function() {
		if(this.pointer <= 0)
			throw new Error('Already at newest record');

		--this.pointer;

		return this.submitted[this.pointer];
	};
	// Go to a higher pointer
	InputHistory.prototype.backward = function() {
		this.submitCallback(this.getBackward());
	};

	// Go towards pointer = 0
	InputHistory.prototype.forward = function() {
		this.submitCallback(this.getForward());
	};

	return InputHistory;
});
define('input-manager/InputManager',[
	'./Request',

	'./InputCursor',
	'./InputSuggestions',
	'./InputHistory'
], function (
	Request,

	InputCursor,
	InputSuggestions,
	InputHistory
) {

	/*
	 * @NOTICE: many of the destroyer functions returned by 'onChange', 'onSubmit' etc. use the "self" variable,
	 *          which is actually called "this". Probably gonna throw out all this code anyway when switching to eventemitter
	 *
	 */

	function InputManager () {
		this.cursor = new InputCursor();
		this.suggestions = new InputSuggestions();
		this.history = new InputHistory(this.submit.bind(this));

		this.submitCallbacks = [];
		this.changeCallbacks = [];
		this.magicHrefCallbacks = [];

		// @notice: also creates this.fieldElement and overlayTextElement
		this.element = this.createElement();

		window.addEventListener('keydown', function(event) {
			if(event.keyCode === 13 && this.getValue().trim())
				this.submitFromForm(event);
		}.bind(this));


		window.addEventListener('click', function(event) {
			this.focusField(true);
		}.bind(this));


		this.fieldElement.addEventListener('blur', function(event) {
			this.focusField(true);
		}.bind(this));

		var lastValue = undefined;

		var changeDetectionLoop = (function () {
			var currentValue = this.getValue(true);
			if(currentValue === lastValue)
				return requestAnimationFrame(changeDetectionLoop);

			this.change(currentValue, false);

			lastValue = currentValue;

			requestAnimationFrame(changeDetectionLoop.bind(this));
		}).bind(this);


		changeDetectionLoop();
	}

	InputManager.prototype.createElement= function() {

		var inputPrefix = document.createElement('span');
		inputPrefix.classList.add('input__prefix');
		inputPrefix.innerHTML = '$';

		var inputField = document.createElement('span');
		inputField.classList.add('input__field');
		inputField.setAttribute('contenteditable', 'true');
		this.fieldElement = inputField;

		var inputOverlayText = document.createElement('span');
		inputOverlayText.classList.add('input__overlay__text');
		this.overlayTextElement = inputOverlayText;

		var inputOverlay = document.createElement('div');
		inputOverlay.appendChild(inputOverlayText);
		inputOverlay.appendChild(this.cursor.element);
		inputOverlay.appendChild(this.suggestions.element);
		inputOverlay.classList.add('input__overlay');

		var inputText = document.createElement('div');
		inputText.classList.add('input__text');
		inputText.appendChild(inputField);
		inputText.appendChild(inputOverlay);

		var inputWrapper = document.getElementById('input');
		inputWrapper.classList.add('input');

		inputWrapper.appendChild(inputPrefix);
		inputWrapper.appendChild(inputText);

		return inputWrapper;
	};

	InputManager.prototype.focusField = function(atEndOfNode) {
		if(atEndOfNode && this.fieldElement.firstChild && this.fieldElement.firstChild.nodeType === 3) {

			var range = document.createRange(),
				node = this.fieldElement.firstChild,
				offset = node.wholeText.length;

			range.setStart(node, offset);
			range.setEnd(node, offset);

			var selection = window.getSelection();
			selection.removeAllRanges();
			selection.addRange(range);
		}
		this.fieldElement.focus();
	};
	InputManager.prototype.getValue = function(raw) {
		return raw ? this.fieldElement.textContent : this.fieldElement.textContent.replace( /\s\s+/g, ' ');
	};

	InputManager.prototype.clearValue = function(clearToText) {
		this.fieldElement.innerHTML = clearToText || '';
	};

	InputManager.prototype.parseCommand = function(value) {
		if(!(value instanceof Request))
			return new Request(value);
		else return value;
	};


	InputManager.prototype.submit = function(value, omitCallbacks) {
		value = value || this.getValue();
		value = typeof value === 'object' ? value :  this.parseCommand(value);

		this.history.onwardIfNotAtPointer(value);

		this.submitCallbacks.forEach(function(callback) {
			callback(value);
		});
	};

	InputManager.prototype.submitFromForm = function(event) {
		if(event && event instanceof KeyboardEvent) {
			event.preventDefault();
			event.stopPropagation();
		}
		this.submit();
		this.clearValue();
	};

	InputManager.prototype.onSubmit = function(callback) {
		this.submitCallbacks.push(callback);

		return function() {
			self.submitCallbacks.splice(self.submitCallbacks.indexOf(callback), 1);
		}.bind(this);
	};


	/**
	 * The act of changing what's displayed as the input, leaves the actual content-editable untouched.
	 *
	 * @param {String}  newValue ~ Raw, that means includes whitespace etc.
	 * @param {Boolean} clear    ~ Overwrite the actual fieldElement value as well,
	 *                             MUST omit when change() is triggered from changeDetectionLoop
	 */
	InputManager.prototype.change = function(newValue, clear) {

		var parsed = this.parseCommand(newValue);

		this.changeCallbacks.forEach(function(callback) {
			callback(parsed);
		});

		if(clear) {
			this.clearValue(newValue);
		}

		this.overlayTextElement.innerHTML = parsed.input;
	};

	/**
	 * Register a callback for the event a change occurs.
	 * @param callback
	 * @returns {function(this:InputManager)} Destroyer function
	 */
	InputManager.prototype.onChange = function(callback) {
		this.changeCallbacks.push(callback);

		return function() {
			self.changeCallbacks.splice(self.changeCallbacks.indexOf(callback), 1);
		}.bind(this);
	};

	InputManager.prototype.onMagicHref = function(callback) {
		this.magicHrefCallbacks.push(callback);

		return function() {
			self.magicHrefCallbacks.splice(self.magicHrefCallbacks.indexOf(callback), 1);
		}.bind(this);
	};

	/**
	 * "submitFromMagicHref", but only if given event is actually a relevant click on
	 * an a@command='command or whatever --yes'.
	 */
	InputManager.prototype.captureMagicHref = function(parent) {
		parent.addEventListener('click', function(event) {
			var target = event.target,
				href = target.getAttribute('command');

			// determine elegibility
			if(!href)
				return;

			// submit
			var parsedInput = this.parseCommand(href);

			// submit some more
			this.magicHrefCallbacks.forEach(function(magicHrefCallback) {
				magicHrefCallback(parsedInput);
			});

			// stop
			event.preventDefault();
		}.bind(this));
	};
	return InputManager;
});
define('input-manager/main',[
	'./InputManager'
], function (
	InputManager
) {
	/**
	 * @TODO: InputHistory is not (?) being used atm
	 */
	return {
		InputManager: InputManager
	}
});
define('input-manager', ['input-manager/main'], function (main) { return main; });

/**
 * @license RequireJS text 2.0.14 Copyright (c) 2010-2014, The Dojo Foundation All Rights Reserved.
 * Available via the MIT or new BSD license.
 * see: http://github.com/requirejs/text for details
 */
/*jslint regexp: true */
/*global require, XMLHttpRequest, ActiveXObject,
  define, window, process, Packages,
  java, location, Components, FileUtils */

define('text',['module'], function (module) {
    'use strict';

    var text, fs, Cc, Ci, xpcIsWindows,
        progIds = ['Msxml2.XMLHTTP', 'Microsoft.XMLHTTP', 'Msxml2.XMLHTTP.4.0'],
        xmlRegExp = /^\s*<\?xml(\s)+version=[\'\"](\d)*.(\d)*[\'\"](\s)*\?>/im,
        bodyRegExp = /<body[^>]*>\s*([\s\S]+)\s*<\/body>/im,
        hasLocation = typeof location !== 'undefined' && location.href,
        defaultProtocol = hasLocation && location.protocol && location.protocol.replace(/\:/, ''),
        defaultHostName = hasLocation && location.hostname,
        defaultPort = hasLocation && (location.port || undefined),
        buildMap = {},
        masterConfig = (module.config && module.config()) || {};

    text = {
        version: '2.0.14',

        strip: function (content) {
            //Strips <?xml ...?> declarations so that external SVG and XML
            //documents can be added to a document without worry. Also, if the string
            //is an HTML document, only the part inside the body tag is returned.
            if (content) {
                content = content.replace(xmlRegExp, "");
                var matches = content.match(bodyRegExp);
                if (matches) {
                    content = matches[1];
                }
            } else {
                content = "";
            }
            return content;
        },

        jsEscape: function (content) {
            return content.replace(/(['\\])/g, '\\$1')
                .replace(/[\f]/g, "\\f")
                .replace(/[\b]/g, "\\b")
                .replace(/[\n]/g, "\\n")
                .replace(/[\t]/g, "\\t")
                .replace(/[\r]/g, "\\r")
                .replace(/[\u2028]/g, "\\u2028")
                .replace(/[\u2029]/g, "\\u2029");
        },

        createXhr: masterConfig.createXhr || function () {
            //Would love to dump the ActiveX crap in here. Need IE 6 to die first.
            var xhr, i, progId;
            if (typeof XMLHttpRequest !== "undefined") {
                return new XMLHttpRequest();
            } else if (typeof ActiveXObject !== "undefined") {
                for (i = 0; i < 3; i += 1) {
                    progId = progIds[i];
                    try {
                        xhr = new ActiveXObject(progId);
                    } catch (e) {}

                    if (xhr) {
                        progIds = [progId];  // so faster next time
                        break;
                    }
                }
            }

            return xhr;
        },

        /**
         * Parses a resource name into its component parts. Resource names
         * look like: module/name.ext!strip, where the !strip part is
         * optional.
         * @param {String} name the resource name
         * @returns {Object} with properties "moduleName", "ext" and "strip"
         * where strip is a boolean.
         */
        parseName: function (name) {
            var modName, ext, temp,
                strip = false,
                index = name.lastIndexOf("."),
                isRelative = name.indexOf('./') === 0 ||
                             name.indexOf('../') === 0;

            if (index !== -1 && (!isRelative || index > 1)) {
                modName = name.substring(0, index);
                ext = name.substring(index + 1);
            } else {
                modName = name;
            }

            temp = ext || modName;
            index = temp.indexOf("!");
            if (index !== -1) {
                //Pull off the strip arg.
                strip = temp.substring(index + 1) === "strip";
                temp = temp.substring(0, index);
                if (ext) {
                    ext = temp;
                } else {
                    modName = temp;
                }
            }

            return {
                moduleName: modName,
                ext: ext,
                strip: strip
            };
        },

        xdRegExp: /^((\w+)\:)?\/\/([^\/\\]+)/,

        /**
         * Is an URL on another domain. Only works for browser use, returns
         * false in non-browser environments. Only used to know if an
         * optimized .js version of a text resource should be loaded
         * instead.
         * @param {String} url
         * @returns Boolean
         */
        useXhr: function (url, protocol, hostname, port) {
            var uProtocol, uHostName, uPort,
                match = text.xdRegExp.exec(url);
            if (!match) {
                return true;
            }
            uProtocol = match[2];
            uHostName = match[3];

            uHostName = uHostName.split(':');
            uPort = uHostName[1];
            uHostName = uHostName[0];

            return (!uProtocol || uProtocol === protocol) &&
                   (!uHostName || uHostName.toLowerCase() === hostname.toLowerCase()) &&
                   ((!uPort && !uHostName) || uPort === port);
        },

        finishLoad: function (name, strip, content, onLoad) {
            content = strip ? text.strip(content) : content;
            if (masterConfig.isBuild) {
                buildMap[name] = content;
            }
            onLoad(content);
        },

        load: function (name, req, onLoad, config) {
            //Name has format: some.module.filext!strip
            //The strip part is optional.
            //if strip is present, then that means only get the string contents
            //inside a body tag in an HTML string. For XML/SVG content it means
            //removing the <?xml ...?> declarations so the content can be inserted
            //into the current doc without problems.

            // Do not bother with the work if a build and text will
            // not be inlined.
            if (config && config.isBuild && !config.inlineText) {
                onLoad();
                return;
            }

            masterConfig.isBuild = config && config.isBuild;

            var parsed = text.parseName(name),
                nonStripName = parsed.moduleName +
                    (parsed.ext ? '.' + parsed.ext : ''),
                url = req.toUrl(nonStripName),
                useXhr = (masterConfig.useXhr) ||
                         text.useXhr;

            // Do not load if it is an empty: url
            if (url.indexOf('empty:') === 0) {
                onLoad();
                return;
            }

            //Load the text. Use XHR if possible and in a browser.
            if (!hasLocation || useXhr(url, defaultProtocol, defaultHostName, defaultPort)) {
                text.get(url, function (content) {
                    text.finishLoad(name, parsed.strip, content, onLoad);
                }, function (err) {
                    if (onLoad.error) {
                        onLoad.error(err);
                    }
                });
            } else {
                //Need to fetch the resource across domains. Assume
                //the resource has been optimized into a JS module. Fetch
                //by the module name + extension, but do not include the
                //!strip part to avoid file system issues.
                req([nonStripName], function (content) {
                    text.finishLoad(parsed.moduleName + '.' + parsed.ext,
                                    parsed.strip, content, onLoad);
                });
            }
        },

        write: function (pluginName, moduleName, write, config) {
            if (buildMap.hasOwnProperty(moduleName)) {
                var content = text.jsEscape(buildMap[moduleName]);
                write.asModule(pluginName + "!" + moduleName,
                               "define(function () { return '" +
                                   content +
                               "';});\n");
            }
        },

        writeFile: function (pluginName, moduleName, req, write, config) {
            var parsed = text.parseName(moduleName),
                extPart = parsed.ext ? '.' + parsed.ext : '',
                nonStripName = parsed.moduleName + extPart,
                //Use a '.js' file name so that it indicates it is a
                //script that can be loaded across domains.
                fileName = req.toUrl(parsed.moduleName + extPart) + '.js';

            //Leverage own load() method to load plugin value, but only
            //write out values that do not have the strip argument,
            //to avoid any potential issues with ! in file names.
            text.load(nonStripName, req, function (value) {
                //Use own write() method to construct full module value.
                //But need to create shell that translates writeFile's
                //write() to the right interface.
                var textWrite = function (contents) {
                    return write(fileName, contents);
                };
                textWrite.asModule = function (moduleName, contents) {
                    return write.asModule(moduleName, fileName, contents);
                };

                text.write(pluginName, nonStripName, textWrite, config);
            }, config);
        }
    };

    if (masterConfig.env === 'node' || (!masterConfig.env &&
            typeof process !== "undefined" &&
            process.versions &&
            !!process.versions.node &&
            !process.versions['node-webkit'] &&
            !process.versions['atom-shell'])) {
        //Using special require.nodeRequire, something added by r.js.
        fs = require.nodeRequire('fs');

        text.get = function (url, callback, errback) {
            try {
                var file = fs.readFileSync(url, 'utf8');
                //Remove BOM (Byte Mark Order) from utf8 files if it is there.
                if (file[0] === '\uFEFF') {
                    file = file.substring(1);
                }
                callback(file);
            } catch (e) {
                if (errback) {
                    errback(e);
                }
            }
        };
    } else if (masterConfig.env === 'xhr' || (!masterConfig.env &&
            text.createXhr())) {
        text.get = function (url, callback, errback, headers) {
            var xhr = text.createXhr(), header;
            xhr.open('GET', url, true);

            //Allow plugins direct access to xhr headers
            if (headers) {
                for (header in headers) {
                    if (headers.hasOwnProperty(header)) {
                        xhr.setRequestHeader(header.toLowerCase(), headers[header]);
                    }
                }
            }

            //Allow overrides specified in config
            if (masterConfig.onXhr) {
                masterConfig.onXhr(xhr, url);
            }

            xhr.onreadystatechange = function (evt) {
                var status, err;
                //Do not explicitly handle errors, those should be
                //visible via console output in the browser.
                if (xhr.readyState === 4) {
                    status = xhr.status || 0;
                    if (status > 399 && status < 600) {
                        //An http 4xx or 5xx error. Signal an error.
                        err = new Error(url + ' HTTP status: ' + status);
                        err.xhr = xhr;
                        if (errback) {
                            errback(err);
                        }
                    } else {
                        callback(xhr.responseText);
                    }

                    if (masterConfig.onXhrComplete) {
                        masterConfig.onXhrComplete(xhr, url);
                    }
                }
            };
            xhr.send(null);
        };
    } else if (masterConfig.env === 'rhino' || (!masterConfig.env &&
            typeof Packages !== 'undefined' && typeof java !== 'undefined')) {
        //Why Java, why is this so awkward?
        text.get = function (url, callback) {
            var stringBuffer, line,
                encoding = "utf-8",
                file = new java.io.File(url),
                lineSeparator = java.lang.System.getProperty("line.separator"),
                input = new java.io.BufferedReader(new java.io.InputStreamReader(new java.io.FileInputStream(file), encoding)),
                content = '';
            try {
                stringBuffer = new java.lang.StringBuffer();
                line = input.readLine();

                // Byte Order Mark (BOM) - The Unicode Standard, version 3.0, page 324
                // http://www.unicode.org/faq/utf_bom.html

                // Note that when we use utf-8, the BOM should appear as "EF BB BF", but it doesn't due to this bug in the JDK:
                // http://bugs.sun.com/bugdatabase/view_bug.do?bug_id=4508058
                if (line && line.length() && line.charAt(0) === 0xfeff) {
                    // Eat the BOM, since we've already found the encoding on this file,
                    // and we plan to concatenating this buffer with others; the BOM should
                    // only appear at the top of a file.
                    line = line.substring(1);
                }

                if (line !== null) {
                    stringBuffer.append(line);
                }

                while ((line = input.readLine()) !== null) {
                    stringBuffer.append(lineSeparator);
                    stringBuffer.append(line);
                }
                //Make sure we return a JavaScript string and not a Java string.
                content = String(stringBuffer.toString()); //String
            } finally {
                input.close();
            }
            callback(content);
        };
    } else if (masterConfig.env === 'xpconnect' || (!masterConfig.env &&
            typeof Components !== 'undefined' && Components.classes &&
            Components.interfaces)) {
        //Avert your gaze!
        Cc = Components.classes;
        Ci = Components.interfaces;
        Components.utils['import']('resource://gre/modules/FileUtils.jsm');
        xpcIsWindows = ('@mozilla.org/windows-registry-key;1' in Cc);

        text.get = function (url, callback) {
            var inStream, convertStream, fileObj,
                readData = {};

            if (xpcIsWindows) {
                url = url.replace(/\//g, '\\');
            }

            fileObj = new FileUtils.File(url);

            //XPCOM, you so crazy
            try {
                inStream = Cc['@mozilla.org/network/file-input-stream;1']
                           .createInstance(Ci.nsIFileInputStream);
                inStream.init(fileObj, 1, 0, false);

                convertStream = Cc['@mozilla.org/intl/converter-input-stream;1']
                                .createInstance(Ci.nsIConverterInputStream);
                convertStream.init(inStream, "utf-8", inStream.available(),
                Ci.nsIConverterInputStream.DEFAULT_REPLACEMENT_CHARACTER);

                convertStream.readString(inStream.available(), readData);
                convertStream.close();
                inStream.close();
                callback(readData.value);
            } catch (e) {
                throw new Error((fileObj && fileObj.path || '') + ': ' + e);
            }
        };
    }
    return text;
});

define('text!output-manager/headerFont.json',[],function () { return '{\n\t"map": " ()abcdefghijklmnopqrstuvwxyz!_-|\\\\/?.,",\n\t"matrix": [\n\t\t"  ",\n\t\t"  ",\n\t\t"  ",\n\t\t"  ",\n\n\t\t"/ ",\n\t\t"| ",\n\t\t"\\\\ ",\n\t\t"  ",\n\n\t\t"\\\\ ",\n\t\t" |",\n\t\t"/ ",\n\t\t"  ",\n\n\t\t"    ",\n\t\t" /\\\\ ",\n\t\t"/~~\\\\",\n\t\t"    ",\n\n\t\t" __ ",\n\t\t"|__)",\n\t\t"|__)",\n\t\t"    ",\n\n\t\t" __ ",\n\t\t"/  `",\n\t\t"\\\\__,",\n\t\t"    ",\n\n\t\t" __ ",\n\t\t"|  \\\\",\n\t\t"|__/",\n\t\t"    ",\n\n\t\t" ___",\n\t\t"|__ ",\n\t\t"|___",\n\t\t"    ",\n\n\t\t" ___",\n\t\t"|__ ",\n\t\t"|   ",\n\t\t"    ",\n\n\t\t" __ ",\n\t\t"/ _`",\n\t\t"\\\\__>",\n\t\t"    ",\n\n\t\t"    ",\n\t\t"|__|",\n\t\t"|  |",\n\t\t"    ",\n\n\t\t" ",\n\t\t"|",\n\t\t"|",\n\t\t" ",\n\n\t\t"    ",\n\t\t"   |",\n\t\t"\\\\__/",\n\t\t"    ",\n\n\t\t"    ",\n\t\t"|__/",\n\t\t"|  \\\\",\n\t\t"    ",\n\n\t\t"    ",\n\t\t"|   ",\n\t\t"|___",\n\t\t"    ",\n\n\t\t"    ",\n\t\t"|\\\\/|",\n\t\t"|  |",\n\t\t"    ",\n\n\t\t"    ",\n\t\t"|\\\\ |",\n\t\t"| \\\\|",\n\t\t"    ",\n\n\t\t" __ ",\n\t\t"/  \\\\",\n\t\t"\\\\__/",\n\t\t"    ",\n\n\t\t" __ ",\n\t\t"|__)",\n\t\t"|   ",\n\t\t"    ",\n\n\t\t" __ ",\n\t\t"/  \\\\",\n\t\t"\\\\__X",\n\t\t"    ",\n\n\t\t" __ ",\n\t\t"|__)",\n\t\t"|  \\\\",\n\t\t"    ",\n\n\t\t" __ ",\n\t\t"/__`",\n\t\t".__/",\n\t\t"    ",\n\n\t\t"___",\n\t\t" | ",\n\t\t" | ",\n\t\t"   ",\n\n\t\t"    ",\n\t\t"|  |",\n\t\t"\\\\__/",\n\t\t"    ",\n\n\t\t"    ",\n\t\t"\\\\  /",\n\t\t" \\\\/ ",\n\t\t"    ",\n\n\t\t"    ",\n\t\t"|  |",\n\t\t"|/\\\\|",\n\t\t"    ",\n\n\t\t"   ",\n\t\t"\\\\_/",\n\t\t"/ \\\\",\n\t\t"   ",\n\n\t\t"   ",\n\t\t"\\\\ /",\n\t\t" | ",\n\t\t"   ",\n\n\t\t"__",\n\t\t" /",\n\t\t"/_",\n\t\t"  ",\n\n\t\t" ",\n\t\t"|",\n\t\t".",\n\t\t" ",\n\n\t\t"   ",\n\t\t"   ",\n\t\t"___",\n\t\t"   ",\n\n\t\t"  ",\n\t\t"__",\n\t\t"  ",\n\t\t"  ",\n\n\t\t"|",\n\t\t"|",\n\t\t"|",\n\t\t"|",\n\n\t\t"  ",\n\t\t"\\\\ ",\n\t\t" \\\\",\n\t\t"  ",\n\n\t\t"  ",\n\t\t" /",\n\t\t"/ ",\n\t\t"  ",\n\n\t\t"__ ",\n\t\t" _|",\n\t\t" . ",\n\t\t"   ",\n\n\t\t" ",\n\t\t" ",\n\t\t".",\n\t\t" ",\n\n\t\t" ",\n\t\t" ",\n\t\t".",\n\t\t"\'"\n\t],\n\t"height": 4\n}';});

define('output-manager/output/Output',[
	'promise'
], function (
	Promise
) {

	function Output() {
		throw new Error('Not implemented');
	}

	Output.prototype.render = function(cb) {
		if(this.element)
			throw new Error ('Already rendered');

		var renderedElement = this.onRender();

		if(!(renderedElement instanceof Promise)) {
			this.element = renderedElement;
			setTimeout(function() {
				cb(this.element);
			}.bind(this), 50);
		} else {
			renderedElement.then(function (element) {
				this.element = element;
				cb(this.element);
			}.bind(this)).catch(function(error) {
				console.error('Promised output render threw error: '+error.stack);
			});

		}
	};

	Output.prototype.clear = function() {
		if(!this.element)
			return;

		this.onClear();

		if(this.element.parentNode)
			this.element.parentNode.removeChild(this.element);

		this.element = null;
	};

	// Helper function to easily create element
	Output.prototype.createElement = function(prefix, text, flags, children) {
		var prefixElement = document.createElement('div');
		prefixElement.innerHTML = prefix;
		prefixElement.classList.add('output-item__prefix');

		var textElement = document.createElement('div');
		textElement.innerHTML = text || this.text || '';
		textElement.classList.add('output-item__text');

		var element = document.createElement('div');
		element.classList.add('output-item');
		element.setAttribute('style', 'top: 2.2rem; opacity: 0;');
		if(flags)
			(typeof flags == 'string' ? flags.split(' ') : flags).forEach(function (flag) {
				this.addFlag(flag, element);
			}.bind(this));

		element.appendChild(prefixElement);
		element.appendChild(textElement);

		if(children)
			children.forEach(function(childElement) {
				element.appendChild(childElement);
			});

		return element;
	};

	Output.prototype.addFlag = function(flag, element) {
		if(!this.flags)
			this.flags = [];

		this.flags.push(flag);

		element = element || this.element;

		if(element)
			element.classList.add('output-item--' + flag);
	};

	Output.prototype.removeFlag = function(flag, element) {
		if(this.flags)
			this.flags.splice(this.flags.indexOf(flag), 1);

		element = element || this.element;

		if(element)
			element.classList.remove('output-item--' + flag);
	};

	Output.prototype.onClear = function() {
		throw new Error('Not implemented');
	};

	Output.prototype.onRender = function() {
		throw new Error('Not implemented');
	};

	return Output;
});

define('output-manager/output/Log',[
	'./Output'
], function (
	Output
	) {

	function Log(text, flags, prefix) {
		this.text = text;
		this.flags = (typeof flags === 'string' ? flags.split(' ') : flags) || ['log'];
		this.prefix = prefix || '>';
	}

	Log.prototype = Object.create(Output.prototype);
	Log.prototype.constructor = Log;

	Log.prototype.onClear = function() {

	};

	Log.prototype.onRender = function() {
		return this.createElement(this.prefix, this.text, this.flags);
	};

	return Log;
});

define('output-manager/output/ErrorLog',[
	'./Output'
], function (
	Output
	) {

	function ErrorLog(error) {
		this.text = error;
	}

	ErrorLog.prototype = Object.create(Output.prototype);
	ErrorLog.prototype.constructor = ErrorLog;

	ErrorLog.prototype.onClear = function() {

	};

	ErrorLog.prototype.onRender = function() {
		var stackElement,
			stackStrings = (this.text.stack || '').split('\n').map(function(stackString) {
				return stackString.trim().replace(window.location.origin, '/var/www');
			});

		stackStrings.shift();

		if(stackStrings.length) {
			stackElement = document.createElement('div');
			stackElement.classList.add('output-item__stack');
			stackElement.classList.add('is-debug');
			stackElement.innerHTML = stackStrings.slice(0, 3).join('<br />');
		}
		return this.createElement('!', this.text, 'error', stackElement ? [stackElement] : null);
	};

	return ErrorLog;
});

define('output-manager/output/DebugLog',[
	'./Output'
], function (
	Output
	) {

	function DebugLog() {
		var args = arguments;
		this.datas = Object.keys(args).map(function(dataKey) {
			return args[dataKey];
		});
	}

	DebugLog.prototype = Object.create(Output.prototype);
	DebugLog.prototype.constructor = DebugLog;

	DebugLog.prototype.onClear = function() {

	};

	DebugLog.prototype.onRender = function() {

		var text = 'Undescribed debug message';

		if(typeof this.datas[0] === 'string') {
			text = this.datas[0];
		}

		return this.createElement('!', text, 'debug', this.datas.filter(function(data) {
			return (data !== text) && (['string', 'number', 'object', 'function'].indexOf(typeof data) >= 0);
		})
		.map(function(data) {
			var dataElement = document.createElement('pre');
			dataElement.classList.add('output-item__debug');
			dataElement.classList.add('is-debug');
			dataElement.innerHTML = typeof data === 'object' ? JSON.stringify(data, null, '  ') : (''+data);
			return dataElement;
		}));
	};

	return DebugLog;
});

define('output-manager/output/KeyValueLog',[
	'./Output'
], function (
	Output
	) {

	function KeyvalueLog(key, value) {
		this.key = key;
		this.value = value;
	}

	KeyvalueLog.prototype = Object.create(Output.prototype);
	KeyvalueLog.prototype.constructor = KeyvalueLog;

	KeyvalueLog.prototype.onClear = function() {

	};

	KeyvalueLog.prototype.onRender = function() {

		return this.createElement('>', this.key || '', 'key-value', [this.value].filter(function(data) {
			return ['string', 'number', 'object'].indexOf(typeof data) >= 0;
		})
		.map(function(data) {
			var dataElement = document.createElement('div');
			dataElement.classList.add('output-item__value');
			dataElement.innerHTML = typeof data === 'object' ? JSON.stringify(data, null, '  ') : (''+data);
			return dataElement;
		}));
	};

	return KeyvalueLog;
});

define('output-manager/output/AsyncLog',[
	'promise',
	'./Output'
], function (
	Promise,
	Output
	) {

	function AsyncLog(text, async, done) {
		this.text = text;
		this.async = async;
		this.done = done;
	}

	AsyncLog.prototype = Object.create(Output.prototype);
	AsyncLog.prototype.constructor = AsyncLog;

	AsyncLog.prototype.onClear = function() {

	};

	AsyncLog.prototype.onRender = function() {
		var spinnerElement = document.createElement('div'),
			element = this.createElement('>', this.text, 'async async-pending', [spinnerElement]),
			async = this.async,
			startTime = new Date().getTime(),
			promise = null;

		spinnerElement.classList.add('output-item__spinner');
		spinnerElement.innerHTML = 'Pending...';

		if(typeof async === 'number') {
			promise = new Promise(function(res) {
				setTimeout(function() {
					res(element)
				}, async || 100);
			});
		} else if(typeof async === 'function') {
			promise = new Promise(function(res, rej) {
				async(function() {
					res(element)
				}, rej);
			});
		} else if(async instanceof Promise) {
			promise = async; // only works if this promise throws
			//throw new Error('Promise not (yet) supported');
		} else {
			throw new Error('Unknown asynchronous log resolve type');
		}

		promise
			.then(function() {
				spinnerElement.innerHTML = (new Date().getTime()) - startTime + ' ms';
				this.addFlag('async-success');

				if(typeof this.done === 'function')
					this.done();
				return spinnerElement;
			}.bind(this))
			.catch(function(e) {
				spinnerElement.innerHTML = 'Failed';
				this.addFlag('async-failed');
				if(typeof this.done === 'function')
					this.done();
				return spinnerElement;
			}.bind(this));
		return promise;
	};

	return AsyncLog;
});

define('output-manager/OutputManager',[
	'text!./headerFont.json',
	'./output/Log',
	'./output/ErrorLog',
	'./output/DebugLog',
	'./output/KeyValueLog',
	'./output/AsyncLog'
], function (
	headerFont,
	Log,
	ErrorLog,
	DebugLog,
	KeyValueLog,
	AsyncLog
) {

	function HeaderFont(configuration) {
		this.height = configuration.height;
		this.characters = this.parseMatrix(configuration.map, configuration.matrix)
	}

	HeaderFont.prototype.parseMatrix = function (map, matrix) {
		if(matrix.length !== map.length * this.height)
			throw new Error('Invalid matrix size, expected '+(map.length * this.height));

		var height = this.height,
			characters = {};

		for(var i = 0; i<map.length; ++i) {
			characters[map.charAt(i).toLowerCase()] = matrix.slice(i * height, (i + 1) * height);
		}
		return characters;
	};

	HeaderFont.prototype.render = function (string) {
		var lines = [];
		for (var j = 0; j < this.height; ++j) {
			lines.push('');
		}

		string = (string || 'undefined').toLowerCase();

		for (var i = 0; i < string.length; ++i) {
			var characterLines = this.characters[string.charAt(i)];
			if(!characterLines)
				continue;
			characterLines.forEach(function(charLine, k) {
				lines[k] += charLine;
			});
		}

		return lines;
	};

	function OutputManager() {
		this.headerFont = new HeaderFont(JSON.parse(headerFont));
		this.queue = [];
		this.rendered = [];
		this.onceQueueFlushedCallbacks = [];
		this.flushing = false;
		this.element = this.createElement();
		this.renderCallbacks = [];
	}

	OutputManager.prototype.onRender = function(callback) {
		this.renderCallbacks.push(callback);

		return function() {
			this.renderCallbacks.splice(this.renderCallbacks.indexOf(callback), 1);
		}.bind(this);
	};

	OutputManager.prototype.createElement = function() {

		var element = document.getElementById('output');
		element.classList.add('output');

		return element;
	};

	OutputManager.prototype.queueOutput = function(output) {
		this.queue.push(output);
		this.renderQueuedOutput();
	};

	OutputManager.prototype.renderQueuedOutput = function() {
		if(this.flushing)
			return;

		if(!this.queue.length) {
			var next = false;
			while(next = this.onceQueueFlushedCallbacks.shift()) {
				next();
			}
			return;
		}

		var output = this.queue.shift();

		this.flushing = true;

		return output.render(function(renderedElement) {
			this.element.appendChild(renderedElement);

			setTimeout(function() {
				renderedElement.removeAttribute('style');
			});

			this.renderCallbacks.forEach(function(callback) {
				callback(this, renderedElement);
			}.bind(this));

			this.rendered.push(output);

			this.flushing = false;

			this.scrollToBottom();
			return this.renderQueuedOutput();
		}.bind(this));
	};

	OutputManager.prototype.scrollToBottom = function() {
		this.element.parentNode.scrollTop = this.element.parentNode.scrollHeight;
	};

	OutputManager.prototype.onceQueueFlushed = function(callback) {
		this.onceQueueFlushedCallbacks.push(callback);
	};

	OutputManager.prototype.pruneRenderedOutput = function(maxLength) {
		while(this.rendered.length > (maxLength||0)) {
			this.rendered.shift().clear();
		}
	};

	OutputManager.prototype.log = function(string, flags) {
		if(typeof string === 'string' && string.indexOf('\n') >= 0)
			string = string.split('\n');
		else if(!string && string !== 0)
			string = null;

		if(Array.isArray(string))
			return string.forEach(function(str) {
				this.log(str, flags);
			}.bind(this));

		this.queueOutput(new Log(string, flags));
	};

	OutputManager.prototype.input = function(req) {
		this.queueOutput(new Log(req.input, ['input'], '$'));
	};

	OutputManager.prototype.header = function(string, flags) {
		this.log.call(this, this.headerFont.render(string), flags);
	};

	OutputManager.prototype.error = function(error) {
		this.queueOutput(new ErrorLog(error));
	};

	OutputManager.prototype.debug = function(text, value) {
		this.queueOutput(new DebugLog(text, value));
	};
	OutputManager.prototype.keyValue = function(key, value) {
		this.queueOutput(new KeyValueLog(key, value));
	};

	OutputManager.prototype.async = function(text, async, done) {
		var asyncLog = new AsyncLog(text, async, done);
		this.queueOutput(asyncLog);
		return asyncLog.promise;
	};

	return OutputManager;
});
define('output-manager/main',[
	'./OutputManager'
], function (
	OutputManager
) {

	return {
		OutputManager: OutputManager
	}
});
define('output-manager', ['output-manager/main'], function (main) { return main; });

define('command-manager/defaultResponses',[
], function () {

	return {
		commandInfo: function commandInfoDefaultResponse(req, res) {

		},
		noCommand: function noCommandDefaultResponse(req, res) {
			res.log('No command');

			var parentCommand = req.command.getCommandForRoute(req.input, true),
				parentRoute = parentCommand.getRoute();
			parentRoute[0] = 'help';
			res.log('See also the help files, <a command="'+parentRoute.join(' ')+'">"'+parentRoute.join(' ')+'"</a>.');
		},
		noController: function noControllerDefaultResponse(req, res) {
			res.log(req.command.getRoute().join('/') +
				' ~ ' +
				(req.command.description ? req.command.description : 'No description'));

			var url = req.command.getRoute();
			url[0] = 'help';
			url = url.join(' ');

			res.error('This command has no controller, consult <a command="'+url+'">help '+req.input+'</a> for usage info');
		}
	};
});
define('command-manager/Command',[
	'./defaultResponses'
], function (defaultResponses
) {

	function Command(name, controller) {
		if(typeof name !== 'string')
			throw new Error('Command name must be a string');

		this.name = name;
		this.options = [];
		this._controller = controller;
	}

	Command.prototype.execute = function(req, res, controller) {
		req.command = this;
		controller = controller || this._controller;

		if(!controller)
			defaultResponses.noController(req, res);
		else
			controller(req, res);
	};

	Command.prototype.listCommands = function() {
		return this.children ? Object.keys(this.children).map(function(key) {
			return this.children[key];
		}.bind(this)) : [];
	};
	Command.prototype.listOptions = function() {
		return this.options;
	};

	Command.prototype.getCommandByName = function(name) {
		return this.children ? this.children[name] : undefined;
	};


	Command.prototype.getCommandsByMatchingName = function(name) {
		if(!name)
			return [];
		return this.listCommands().filter(function(command) {
			return command.name.indexOf(name) === 0;
		});
	};

	Command.prototype.getCommandForRoute = function(route, returnClosestMatch) {
		var parentCommand = this,
			lastCommand;

		for (var i = 0; i < route.length; ++i) {
			lastCommand = parentCommand.getCommandByName(route[i]);

			if(lastCommand) {
				parentCommand = lastCommand;

				if(parentCommand.greedy)
					break;

				continue;
			}

			if (returnClosestMatch)
					break;

			var parentRoute = parentCommand.getRoute().splice(1);

			throw new Error('Invalid segment, command "'+route[i]+'"  cannot be found in "'+parentRoute.join(' ')+'", <a command="help '+parentRoute.join(' ')+'">see help page</a>.');
		}

		return parentCommand || this;
	};

	Command.prototype.getLineage = function() {
		var lineage = [],
			self = this; // highest-level parents first, closest last
		do {
			lineage.unshift(self);
		} while(self = self.getParent());

		return lineage;
	};

	Command.prototype.getRoute = function() {
		return this.getLineage().map(function(command) {
			return command.name;
		})
	};

	Command.prototype.setParent = function(command) {
		if(!command instanceof Command)
			throw new Error('Parent is of wrong type');

		this.parent = command;

		return this;
	};

	Command.prototype.getParent = function() {
		return this.parent;
	}
	Command.prototype.isGreedy = function(isGreedy) {
		this.greedy = isGreedy === undefined ? true : !!isGreedy;

		return this;
	};

	Command.prototype.addDescription = function(description) {
		this.description = Array.isArray(description) ? description : [description];

		return this;
	};
	Command.prototype.addResult = function(result) {
		this.result = result;

		return this;
	};
	Command.prototype.addExample = function(example) {
		this.example = example;

		return this;
	};

	/**
	 *
	 * @param long
	 * @param [short]
	 * @param [description]
	 * @param [required]
	 * @param [type]
	 * @param [example]
	 * @returns {Command}
	 */
	Command.prototype.addOption = function(long, short, description, required, type, example) {
		if(this.options.length && this.options.some(function(opt) {
			return opt.long === long || (short && short === opt.short);
		}))
			throw new Error('Already an option with either this long "' + long + '" or short  "' + short + '"');

		this.options.push({
			long: long,
			short: short,
			description: description,
			required: !!required,
			type: type,
			example: example
		});

		return this;
	};

	Command.prototype.addCommand = function(name, controller) {

		var child = name instanceof Command ? name : new Command(name, controller);

		if(this.children && this.children[child.name])
			throw Error('Child "' + name + '" already exists');

		child.setParent(this);

		if(!this.children)
			this.children = {};

		this.children[name] = child;

		return child;
	};


	Command.prototype.getSuggestedCommandsForInput = function(value) {
		var parentCommand = this.getCommandForRoute(value.route, true),
			needsAllSuggestion = !value.input.charAt(value.input.length-1).trim(); // last character is a space, or

		return parentCommand.greedy ? [] : (needsAllSuggestion
				? parentCommand.listCommands()
				: parentCommand.getCommandsByMatchingName(value.route[value.route.length-1]));
	};

	return Command;
});
define('command-manager/CommandManager',[
	'./Command',
	'./defaultResponses'
], function (
	Command,
	defaultResponses
) {

	function CommandManager(name) {
		Command.call(this, name || 'root', function(req, res) {
			res.error('Patient zero')
		});

		this.defaults = defaultResponses;
	}

	CommandManager.prototype = Object.create(Command.prototype);
	CommandManager.prototype.constructor = Object.create(CommandManager);

	CommandManager.prototype.executeCommandForRequest = function(req, res) {
		var command;

		try {
			command = this.getCommandForRoute(req.route);
		} catch(e) {
			res.log('Could not execute your command "'+req.input+'" because an error occurred:');
			res.error(e);
			return;
		}

		// normalize (delete) short flags for their long counterparts
		command.options.forEach(function(option) {
			if(req.options[option.short]) {
				if(req.options[option.long] === undefined) {
					req.options[option.long] = req.options[option.short];
				}
				delete req.options[option.short];
			}
		});

		command.execute(req, res);
	};

	return CommandManager;
});
define('command-manager/main',[
	'./CommandManager'
], function (
	CommandManager
) {

	return {
		CommandManager: CommandManager
	};
});
define('command-manager', ['command-manager/main'], function (main) { return main; });

define('window-manager/DraggableElement',[], function () {
	'use strict';
	function findClosestAncestor(node, condition) {
		while (node && !condition(node)) {
			node = node.parentNode;
		}
		return node;
	}

	function isElementIsDescendantOf(child, parent) {
		return !!findClosestAncestor(child, function (node) {
			return node === parent;
		});
		//do {
		//	if(child == parent)
		//		return true;
		//	child = child.parentNode;
		//} while(child != null);
		//
		//return false;
	}

	function DraggableElement (element, allowDragOutside) {
		this.dragElement = element;
		this.dragging = false;

		this.dragCallbacks = [];
		this.dragStartCallbacks = [];
		this.dragStopCallbacks = [];

		// Each attribute in dragInfo is either {x:x,y:y} or false
		this.dragInfo = {
			started: false,
			offset: false,
			delta: false,
			stopped: false
		};

		this.dragElement.classList.add('draggable');

		this.onDrag = this.onDrag.bind(this);

		this.addDragHandlers = function(mouseEvent) {

			if(findClosestAncestor(mouseEvent.target, function (node) {
				return node.classList.contains('draggable');
			}) !== this.dragElement)
				return;

			mouseEvent.preventDefault();
			mouseEvent.stopPropagation();
			//mouseEvent.stopImmediatePropagation();
			//
			//if(!isElementIsDescendantOf(mouseEvent.target, this.dragElement)) {
			//	return;
			//}

			if(mouseEvent.which === 3 || mouseEvent.button === 2) {
				return;
			}

			window.addEventListener("mousemove", this.onDrag);
			window.addEventListener("mouseup", this.removeDragHandlers);
			if(!allowDragOutside)
				element.addEventListener("mouseleave", this.removeDragHandlers);
			element.removeEventListener("mousedown", this.addDragHandlers);
		}.bind(this);

		this.removeDragHandlers = function(mouseEvent) {
			mouseEvent.preventDefault();
			mouseEvent.stopPropagation();
			//mouseEvent.stopImmediatePropagation();

			this.onDragStop(mouseEvent);

			window.removeEventListener("mousemove", this.onDrag);
			window.removeEventListener("mouseup", this.removeDragHandlers);
			if(!allowDragOutside)
				element.removeEventListener("mouseleave", this.removeDragHandlers);
			element.addEventListener("mousedown", this.addDragHandlers);
		}.bind(this);
	}

	DraggableElement.prototype.getElement = function() {
		return this.dragElement;
	};

	// start listening for new drag actions
	DraggableElement.prototype.setListeners = function () {
		this.dragElement.addEventListener("mousedown", this.addDragHandlers, true);
	};

	DraggableElement.prototype.attachToParent = function(parentElement) {
		parentElement.appendChild(this.getElement());
		this.setListeners();
	};

	DraggableElement.prototype.detachFromParent = function(omitCallbacks) {
		var element = this.getElement(),
			parent = element.parentNode;

		if(parent) {
			parent.removeChild(element);
		}
		this.removeListeners();
	};

	// stop listening for new drag actions
	DraggableElement.prototype.removeListeners = function () {
		this.dragElement.removeEventListener("mousedown", this.addDragHandlers, true);
	};

	// When user releases mouse (anywhere) after dragging
	DraggableElement.prototype.onDragStop = function(dragStopEvent) {
		dragStopEvent.preventDefault();
		dragStopEvent.stopPropagation();
		//dragStopEvent.stopImmediatePropagation();

		this.dragging = false;

		this.dragInfo.stopped = {
			x: dragStopEvent.clientX,
			y: dragStopEvent.clientY
		};

		if(this.dragInfo.started && this.dragInfo.relative && this.dragInfo.delta) {
			this.dragStopCallbacks.forEach(function (callback) {
				callback(this.dragInfo);
			}.bind(this));
		}

		this.dragInfo = {
			started: false,
			offset: false,
			delta: false,
			stopped: false
		};
	};

	// When user clicks and holds the mouse, and then drag at least 1px
	DraggableElement.prototype.onDragStart = function(dragStartEvent) {
		dragStartEvent.preventDefault();
		dragStartEvent.stopPropagation();
		//dragStartEvent.stopImmediatePropagation();

		this.dragging = true;
		this.dragInfo = {
			started: {
				x: dragStartEvent.clientX,
				y: dragStartEvent.clientY
			},
			delta: {
				x: 0,
				y: 0
			},
			stopped: false
		};

		this.dragInfo.relative = this.getRelativeForAbsoluteCoords(this.dragInfo.started);

		this.dragStartCallbacks.forEach(function (callback) {
			callback(this.dragInfo);
		}.bind(this));
	};

	// Whenever an element was or is being dragged
	DraggableElement.prototype.onDrag = function(dragEvent) {
		dragEvent.preventDefault();
		dragEvent.stopPropagation();
		//dragEvent.stopImmediatePropagation();

		if (!this.dragging) {
			this.onDragStart(dragEvent);
		}
		this.dragInfo.delta = {
			x: dragEvent.clientX - this.dragInfo.started.x,
			y: dragEvent.clientY - this.dragInfo.started.y
		};

		this.dragCallbacks.forEach(function (callback) {
			callback(this.dragInfo);
		}.bind(this));
	};

	// Get coordinates relative to the top-left of container
	DraggableElement.prototype.getRelativeForAbsoluteCoords = function(coordinates) {
		var boundingBox = this.dragElement.getBoundingClientRect();
		return {
			x: coordinates.x - boundingBox.left,
			y: coordinates.y - boundingBox.top
		};
	};

	// execute everything that should happen when a drag occurs
	// returns a destroyer fn
	DraggableElement.prototype.addDragCallback = function (callback){
		this.dragCallbacks.push(callback);

		return function () {
			this.dragCallbacks.splice(this.dragCallbacks.indexOf(callback), 1);
		}.bind(this);
	};

	// execute everything that should happen when the first pixel of a drag is detected
	// returns a destroyer fn
	DraggableElement.prototype.addDragStartCallback = function (callback){
		this.dragStartCallbacks.push(callback);

		return function () {
			this.dragStartCallbacks.splice(this.dragStartCallbacks.indexOf(callback), 1);
		}.bind(this);
	};

	// execute everything that should happen when the drag is ended
	// returns a destroyer fn
	DraggableElement.prototype.addDragStopCallback = function (callback){
		this.dragStopCallbacks.push(callback);

		return function () {
			this.dragStopCallbacks.splice(this.dragStopCallbacks.indexOf(callback), 1);
		}.bind(this);
	};

	return DraggableElement;
});
(function (factory) {
	/**
	 * AMD, RequireJS
	 */
	if (typeof define === 'function' && define.amd) {
		define('object-store',[], function () {
			return factory();
		});
	}

	/**
	 * CommonJS, NodeJS
	 */
	else if (typeof module === 'object' && module.exports) {
		module.exports = factory();
	}

	else if (window) {
		window.ObjectStore = factory();
	}
}(function () {

	/**
	 * @private
	 * @param {Object} object
	 * @param {Object} changes
	 * @returns {Object}
	 */
	function mergeRecursive(object, changes) {
		Object.keys(changes).forEach(function(propertyName){
			if ( changes[propertyName].constructor == Object ) {
				object[propertyName] = mergeRecursive(object[propertyName], changes[propertyName]);
			} else {
				object[propertyName] = changes[propertyName];
			}
        });
		return object;
	}

	/**
	 * @author wvbe <wybe@x-54.com>
	 *
	 * @constructor
	 * @param {Function} [options.requireInstanceOf] If set, require objects to be an instance of this class
	 * @param {String|Number} [options.primaryKey] Name of the key to use as identifying property, defaults to "id"
	 * @param {Boolean} [options.cacheList] If set, get list() results from cache
	 */
	function ObjectStore (options) {
		var store = {},
			cachedList = null;

		options                   = options                   || {};
		options.requireInstanceOf = options.requireInstanceOf || false;
		options.primaryKey        = options.primaryKey        || 'id';
		options.cacheList         = !!options.cacheList;

		/**
		 * @method get
		 * @param {String|Number} objectKey
		 * @returns {Object}
		 */
		function get(objectKey) {
			if (!objectKey)
				throw new Error('No objectKey given');

			return store[objectKey];
		}

		/**
		 * @method set
		 * @param {Object} object
		 * @param {Boolean} [overwrite]
		 * @returns {Object}
		 */
		function set(object, overwrite) {
			if (!object)
				throw new Error('No object given');
			if (!object[options.primaryKey])
				throw new Error('No objectKey in object');
			if (options.requireInstanceOf && !(object instanceof options.requireInstanceOf))
				throw new Error('ObjectData is not of the right class');

			if (!overwrite && store[object[options.primaryKey]])
				throw new Error('Object "' + object[options.primaryKey] + '" already exists, overwrite not set');

			if (options.cacheList)
				cachedList = null;

			store[object[options.primaryKey]] = object;

			return store[object[options.primaryKey]];
		}

		/**
		 * @method delete
		 * @param {String|Number} objectKey
		 * @returns {*}
		 */
		function del(objectKey) {
			if (!objectKey)
				throw new Error('No objectKey given');

			if (options.cacheList)
				cachedList = null;

			delete store[objectKey];

			return store[objectKey];
		}

		/**
		 * @method list
		 * @returns {Array<Object>}
		 */
		function list() {
			if (options.cacheList && cachedList)
				return cachedList;

			var l = Object.keys(store).map(function (objectKey) {
				return store[objectKey];
			});

			if (options.cacheList)
				cachedList = l;

			return l;
		}

		/**
		 * @method merge
		 * @param {Object} object
		 * @returns {Object}
		 */
		function merge(object) {
			if (!object)
				throw new Error('No object given');
			if (!object[options.primaryKey])
				throw new Error('No objectKey given');

			var objectExisting = get(object[options.primaryKey]);

			if (!objectExisting)
				throw new Error('ObjectKey ' + object[options.primaryKey] + ' does not exist');

			return mergeRecursive(objectExisting, object);
		}

		/**
		 * @method contains
		 * @param {Object} object
		 * @returns {Boolean}
		 */
		function contains(object) {
			return list().indexOf(object) >= 0;
		}

		this.get = get;
		this.set = set;
		this.merge = merge;
		this.delete = del;
		this.list = list;
		this.contains = contains;
	}

	return ObjectStore;
}));
(function(f){if(typeof exports==="object"&&typeof module!=="undefined"){module.exports=f()}else if(typeof define==="function"&&define.amd){define('tiny-emitter',[],f)}else{var g;if(typeof window!=="undefined"){g=window}else if(typeof global!=="undefined"){g=global}else if(typeof self!=="undefined"){g=self}else{g=this}g.TinyEmitter = f()}})(function(){var define,module,exports;return (function e(t,n,r){function s(o,u){if(!n[o]){if(!t[o]){var a=typeof require=="function"&&require;if(!u&&a)return a(o,!0);if(i)return i(o,!0);var f=new Error("Cannot find module '"+o+"'");throw f.code="MODULE_NOT_FOUND",f}var l=n[o]={exports:{}};t[o][0].call(l.exports,function(e){var n=t[o][1][e];return s(n?n:e)},l,l.exports,e,t,n,r)}return n[o].exports}var i=typeof require=="function"&&require;for(var o=0;o<r.length;o++)s(r[o]);return s})({1:[function(require,module,exports){
function E () {
	// Keep this empty so it's easier to inherit from
  // (via https://github.com/lipsmack from https://github.com/scottcorgan/tiny-emitter/issues/3)
}

E.prototype = {
	on: function (name, callback, ctx) {
    var e = this.e || (this.e = {});

    (e[name] || (e[name] = [])).push({
      fn: callback,
      ctx: ctx
    });

    return this;
  },

  once: function (name, callback, ctx) {
    var self = this;
    function listener () {
      self.off(name, listener);
      callback.apply(ctx, arguments);
    };

    listener._ = callback
    return this.on(name, listener, ctx);
  },

  emit: function (name) {
    var data = [].slice.call(arguments, 1);
    var evtArr = ((this.e || (this.e = {}))[name] || []).slice();
    var i = 0;
    var len = evtArr.length;

    for (i; i < len; i++) {
      evtArr[i].fn.apply(evtArr[i].ctx, data);
    }

    return this;
  },

  off: function (name, callback) {
    var e = this.e || (this.e = {});
    var evts = e[name];
    var liveEvents = [];

    if (evts && callback) {
      for (var i = 0, len = evts.length; i < len; i++) {
        if (evts[i].fn !== callback && evts[i].fn._ !== callback)
          liveEvents.push(evts[i]);
      }
    }

    // Remove event from queue to prevent memory leak
    // Suggested by https://github.com/lazd
    // Ref: https://github.com/scottcorgan/tiny-emitter/commit/c6ebfaa9bc973b33d110a84a307742b7cf94c953#commitcomment-5024910

    (liveEvents.length)
      ? e[name] = liveEvents
      : delete e[name];

    return this;
  }
};

module.exports = E;

},{}]},{},[1])(1)
});
define('window-manager/Fucktard',[], function() {

	function Fucktard(x,y) {
		this.element = document.createElement('hr');
		this.element.classList.add('straight-line');
		this.element.style.top = y + 'px';
		this.element.style.left = x + 'px';
	}

	Fucktard.prototype.update = function (delta) {
		this.element.style.transform = 'rotate(' + this.getAngleForDelta(delta) + 'deg)';
		this.element.style.width = this.getLengthForDelta(delta) + 'px';
	};

	Fucktard.prototype.getAngleForDelta = function(delta) {
		var angle = Math.atan2(-1 * delta.y, delta.x);

		if(delta.y > 0) {
			angle = 2 * Math.PI + angle;
		}

		return -(angle * 180 / Math.PI);
	};

	Fucktard.prototype.getLengthForDelta = function(delta) {
		return Math.sqrt(delta.x*delta.x + delta.y*delta.y);
	};

	return Fucktard;
});
define('window-manager/windows/Window',[
	'promise',
	'tiny-emitter',

	'./../DraggableElement',
	'./../Fucktard'
], function (
	Promise,
	TinyEmitter,

	DraggableElement,
	Fucktard
	) {
	'use strict';

	var FUCKTARD_PADDING = 0;

	//@TODO: implement addDestroyer() method for additional destroying of contained scripts etc. when the window closes
	function Window (id, name) {
		TinyEmitter.call(this);
		if(!name || typeof name !== 'string')
			throw new Error('Window needs to have a name');

		this.id = id;
		this.name = name;
		this.flags = [];
		this.anchorDestroyers = [];
		this.destroyCallbacks = [];
		this.isResizable = true;

		if(!id)
			this.generateId();

		this.addFlag('mediumized');
	}

	Window.prototype = Object.create(TinyEmitter.prototype);
	Window.prototype.constructor = Window;

	Window.prototype.destroy = function() {
		this.detachFromParent();

		this.destroyCallbacks.forEach(function(callback) {
			callback();
		});
	};

	// untested
	Window.prototype.detachFromParent = function() {
		while(this.anchorDestroyers.length > 0) {
			this.anchorDestroyers.pop()();
		}

		this.anchor.detachFromParent();

		if (this.isResizable)
			this.resizeAnchor.detachFromParent();
	};

	Window.prototype.attachToParent = function(parentNode) {
		var element = this.element;
		var anchor = this.anchor;
		var resizeAnchor = this.resizeAnchor;

		var dragStartPosition = null,
			ghostElement = null,
			infoElement = null,
			fucktards = [];

		function createGhostAndFucktards () {
			dragStartPosition = element.getBoundingClientRect();
			ghostElement = document.createElement('div');
			//ghostElement.classList.add('window');
			ghostElement.classList.add('window--ghost');
			infoElement = document.createElement('div');
			ghostElement.style.top = (dragStartPosition.top-FUCKTARD_PADDING) + 'px';
			ghostElement.style.left = (dragStartPosition.left-FUCKTARD_PADDING) + 'px';
			ghostElement.style.width = (dragStartPosition.width+2*FUCKTARD_PADDING) + 'px';
			ghostElement.style.height = (dragStartPosition.height+2*FUCKTARD_PADDING) + 'px';

			ghostElement.appendChild(infoElement);
			parentNode.insertBefore(ghostElement, parentNode.firstChild);

			fucktards.push(new Fucktard(FUCKTARD_PADDING, FUCKTARD_PADDING));
			fucktards.push(new Fucktard(dragStartPosition.width, FUCKTARD_PADDING));
			fucktards.push(new Fucktard(dragStartPosition.width, dragStartPosition.height));
			fucktards.push(new Fucktard(FUCKTARD_PADDING, dragStartPosition.height));

			fucktards.forEach(function(fucktard) {
				ghostElement.appendChild(fucktard.element);
			});
		}

		function destroyGhost () {
			fucktards = [];
			dragStartPosition = null;

			if(!ghostElement || !ghostElement.parentNode)
				return;
			ghostElement.parentNode.removeChild(ghostElement);
		}


		this.addDestroyCallback(destroyGhost);

		parentNode.appendChild(element);

		anchor.setListeners();
		if (this.isResizable) {
			this.anchorDestroyers.push(resizeAnchor.addDragStartCallback(function (position) {
				this.emit('touched');
				this.addFlag('resizing');
				createGhostAndFucktards();
			}.bind(this)));

			this.anchorDestroyers.push(resizeAnchor.addDragCallback(function (position) {
				if (!dragStartPosition)
					return;

				var deltaLength = Math.sqrt(position.delta.x * position.delta.x + position.delta.y * position.delta.y);

				infoElement.innerHTML = [
					'<span label="id">' + this.id + '</span>',
					'<span label="name">' + this.name + '</span>',
					'<span label="start">(' + position.started.x + ', ' + position.started.y + ')</span>',
					'<span label="delta">(' + position.delta.x + ', ' + position.delta.y + ') ' + Math.round(deltaLength * 10) / 10 + 'px</span>',
					'<span label="current">(' + (position.started.x + position.delta.x) + ', ' + (position.started.y + position.delta.y) + ')</span>'
				].join('<br />');

				ghostElement.style.width = parseFloat(dragStartPosition.width) + position.delta.x + 'px';
				ghostElement.style.height = parseFloat(dragStartPosition.height) + position.delta.y + 'px';

				var ghostBoundingBox = ghostElement.getBoundingClientRect(),
					ghostDelta = {
						x: ghostBoundingBox.width - dragStartPosition.width,
						y: ghostBoundingBox.height - dragStartPosition.height
					};
				fucktards[2].update(ghostDelta);

				//fucktards.forEach(function(fucktard) {
				//	fucktard.update(position.delta);
				//});
			}.bind(this)));

			this.anchorDestroyers.push(resizeAnchor.addDragStopCallback(function (position) {

				element.style.width = parseFloat(dragStartPosition.width) + position.delta.x + 'px';
				element.style.height = parseFloat(dragStartPosition.height) + position.delta.y + 'px';

				this.removeFlag('resizing');
				this.emit('resized', position);

				destroyGhost();
			}.bind(this)));
		}

		// Move handler
		this.anchorDestroyers.push(anchor.addDragStartCallback(function(position) {
			this.emit('touched');
			this.addFlag('moving');
			createGhostAndFucktards();
		}.bind(this)));

		this.anchorDestroyers.push(anchor.addDragCallback(function(position) {
			if(!dragStartPosition)
				return;

			var deltaLength = Math.sqrt(position.delta.x*position.delta.x + position.delta.y*position.delta.y);
			infoElement.innerHTML = [
					'<span label="id">'+this.id + '</span>',
					'<span label="name">'+this.name + '</span>',
					'<span label="start">('+position.started.x+', '+position.started.y + ')</span>',
					'<span label="delta">('+position.delta.x+', '+position.delta.y + ') '+Math.round(deltaLength*10)/10+'px</span>',
					'<span label="current">('+(position.started.x+position.delta.x)+', '+(position.started.y+position.delta.y) + ')</span>'
			].join('<br />');

			element.style.top = parseFloat(dragStartPosition.top) + position.delta.y + 'px';
			element.style.left = parseFloat(dragStartPosition.left) + position.delta.x + 'px';

			fucktards.forEach(function(fucktard) {
				fucktard.update(position.delta);
			});
		}.bind(this)));


		// Remove ghost when anchors are released;
		this.anchorDestroyers.push(anchor.addDragStopCallback(function(position) {
			this.removeFlag('moving');
			this.emit('moved', position);
			destroyGhost();
		}.bind(this)));


	};



	Window.prototype.generateId = function() {
		var randomInt = 1000 + Math.round(Math.random() * 8999);
		this.id = this.name.substr(0, 4).trim().toUpperCase() + '-' + randomInt;
	};

	Window.prototype.createHeaderElement = function(controls, prefix) {
		prefix = prefix || 'window';

		var titleElement = document.createElement('h1');
		titleElement.classList.add(prefix + '__title');
		titleElement.appendChild(document.createTextNode(this.name));
		titleElement.setAttribute('label', this.id);

		var controlsElement = document.createElement('div');
		controlsElement.classList.add(prefix + '__controls');

		(controls || []).forEach(function(controlElement) {
			controlElement.classList.add(prefix + '__control')
			controlsElement.appendChild(controlElement);
		});

		var headerElement = document.createElement('header');
		headerElement.classList.add(prefix + '__header');
		headerElement.appendChild(titleElement);
		headerElement.appendChild(controlsElement);

		return headerElement;
	};

	Window.prototype.createElement = function(controlElements) {
		if(this.element)
			throw new Error('Already made window element');

		var element = document.createElement('article');
		element.classList.add('window');
		element.setAttribute('window-name', this.name);

		var headerElement = this.createHeaderElement(controlElements);

		var contentElement = this.createContentElement();
		contentElement.classList.add('window__content');

		element.appendChild(headerElement);
		element.appendChild(contentElement);

		// make draggable
		if(this.isResizable) {
			var resizeElement = document.createElement('div');
			resizeElement.classList.add('window__resize');
			resizeElement.setAttribute('title', 'Drag to resize the window');
			element.appendChild(resizeElement);
			this.resizeAnchor = new DraggableElement(resizeElement, true);
			this.resizeAnchor.setListeners();
		}

		this.anchor = new DraggableElement(element, true);
		this.anchor.setListeners();


		this.flags.forEach(function(flag) {
			element.classList.add('window--'+flag);
		});

		this.element = element;
		this.contentElement = contentElement;

		this.element.style.top = 30 + Math.random() * 300 + 'px';
		this.element.style.left = 30 + Math.random() * 400 + 'px';

		return element;
	};

	Window.prototype.createContentElement = function() {
		throw new Error('Not implemented');
	};

	Window.prototype.hasFlag = function (flag) {
		return this.flags.indexOf(flag) >= 0;
	};
	Window.prototype.addFlag = function (flag) {
		if(!this.hasFlag(flag))
			this.flags.push(flag);
		if(this.element)
			this.element.classList.add('window--'+flag);
	};
	Window.prototype.removeFlag = function (flag) {
		if(this.hasFlag(flag))
			this.flags.splice(this.flags.indexOf(flag), 1);
		if(this.element)
			this.element.classList.remove('window--'+flag);
	};

	Window.prototype.addDestroyCallback = function (callback) {
		this.destroyCallbacks.push(callback);
	};

	Window.prototype.minimize = function() {
		return new Promise(function (res) {
				this.addFlag('closing');
				setTimeout(function () {
					res(true);
				}.bind(this), 750);
			}.bind(this))
			.then(function () {
				this.removeFlag('closing');
				this.addFlag('minimized');
				this.removeFlag('maximized');
				this.removeFlag('mediumized');
			}.bind(this));
	};
	Window.prototype.maximize = function() {
		return new Promise(function (res) {
			this.removeFlag('minimized');
			this.removeFlag('mediumized');
			this.addFlag('maximized');
			res(true);
		}.bind(this));
	};
	Window.prototype.mediumize = function() {
		return new Promise(function (res) {
			this.addFlag('mediumized');
			this.removeFlag('minimized');
			this.removeFlag('maximized');
			res(true);
		}.bind(this));
	};
	return Window;
});
define('window-manager/windows/BasicWindow',[
	'./Window'
], function (
	Window
	) {
	function BasicWindow (id, name, content) {
		Window.call(this, id, name);

		this.content = content;

		this.addFlag('basic');
	}

	BasicWindow.prototype = Object.create(Window.prototype);
	BasicWindow.prototype.constructor = BasicWindow;

	BasicWindow.prototype.createContentElement = function() {
		return this.content;
	};

	return BasicWindow;
});
define('window-manager/WindowManager',[
	'object-store',

	'./windows/Window',
	'./windows/BasicWindow'
], function (
	ObjectStore,

	Window,
	BasicWindow
) {

	function WindowTaskbar(element) {
		this.element = element;
		this.element.classList.add('taskbar');
	}
	WindowTaskbar.prototype.update = function(windowManager) {
		this.element.innerHTML = '';

		windowManager.list().forEach(function(window) {
			var controlElements = windowManager.createControlElements(window);

			var headerElement = window.createHeaderElement(controlElements, 'taskbar');

			window.flags.forEach(function(flag) {
				headerElement.classList.add('taskbar--'+flag);
			});

			this.element.appendChild(headerElement);
		}.bind(this));
	};

	function WindowManager () {
		ObjectStore.call(this, {
			requireInstanceOf: Window
		});

		var taskbarElement = document.getElementById('taskbar');
		if(taskbarElement)
			this.taskbar = new WindowTaskbar(taskbarElement);

		this.newWindowCallbacks = [];
		this.destroyWindowCallbacks = [];

		this.element = this.createElement();
	}

	WindowManager.prototype = Object.create(ObjectStore.prototype);
	WindowManager.prototype.constructor = WindowManager;

	WindowManager.prototype.minimize = function(window) {
		return window.minimize().then(function () {
			if(this.taskbar)
				this.taskbar.update(this);
		}.bind(this));
	};

	WindowManager.prototype.mediumize = function(window) {
		return window.mediumize().then(function () {
			if(this.taskbar)
				this.taskbar.update(this);
		}.bind(this));
	};

	WindowManager.prototype.maximize = function(window) {
		this.list().forEach(function(listWindow) {
			if(window === listWindow) {
				window.maximize();
			} else {
				window.minimize();
			}
		});

		if(this.taskbar)
			this.taskbar.update(this);
	};

	WindowManager.prototype.createElement= function() {
		var element = document.getElementById('windows');
		element.classList.add('windows');
		return element;
	};

	WindowManager.prototype.createControlElements = function (window)  {
		var controlElements = [];

		controlElements.push(function (scope, methodName, titleContent) {
			var element = document.createElement('div');
			element.classList.add('taskbar__' + methodName);
			element.setAttribute('title', titleContent);
			element.innerHTML = '-';
			element.addEventListener('click', function() {
				scope[methodName](window);
			});
			return element;
		}(this, 'minimize', 'Click to minimize this window.'));

		controlElements.push(function (scope, methodName, titleContent) {
			var element = document.createElement('div');
			element.classList.add('taskbar__' + methodName);
			element.setAttribute('title', titleContent);
			element.innerHTML = '&#9633;'; // WHITE SQUARE http://www.fileformat.info/info/unicode/char/25A1/index.htm
			element.addEventListener('click', function() {
				scope[methodName](window);
			});
			return element;
		}(this, 'mediumize', 'Click to open this window.'));

		var closeElement = document.createElement('div');
		closeElement.classList.add('window__close');
		closeElement.setAttribute('title', 'Click to close this window.');
		closeElement.innerHTML = '&times;';
		closeElement.addEventListener('click', function() {
			window.addFlag('closing');
			setTimeout(function () {
				window.destroy();
			}, 750);
		});
		controlElements.push(closeElement);

		return controlElements;
	};

	WindowManager.prototype.onNewWindow = function(callback) {
		this.newWindowCallbacks.push(callback);

		return function() {
			this.newWindowCallbacks.splice(this.newWindowCallbacks.indexOf(callback), 1);
		}.bind(this);
	};

	WindowManager.prototype.openNewWindow = function(name, content, id, WindowClass) {
		if(!WindowClass)
			WindowClass = BasicWindow;

		var window = name instanceof Window
			? name
			: new WindowClass(id, name, content);

		window = this.set(window);

		window.createElement(this.createControlElements(window));

		var list = this.list();

		window.element.style.zIndex = list.length;

		window.on('touched', function() {
			this.list().sort(function(a, b) {
				return a.element.style.zIndex === b.element.style.zIndex ? 0 : a.element.style.zIndex - b.element.style.zIndex;
			}).forEach(function(win, i, windows) {
				win.element.style.zIndex = (window === win ? windows.length : i) + 1;
			});
		}.bind(this));


		window.addDestroyCallback(function() {
			this.delete(window.id);
		}.bind(this));

		this.newWindowCallbacks.forEach(function(callback) {
			callback(window);
		});

		window.attachToParent(this.element);

		if(this.taskbar) {
			window.addDestroyCallback(function () {
				this.taskbar.update(this);
			}.bind(this));

			this.taskbar.update(this);
		}
		return window;
	};

	return WindowManager;
});
// Released under MIT license
// Copyright (c) 2009-2010 Dominic Baggott
// Copyright (c) 2009-2010 Ash Berlin
// Copyright (c) 2011 Christoph Dorn <christoph@christophdorn.com> (http://www.christophdorn.com)

/*jshint browser:true, devel:true */

(function( expose ) {

/**
 *  class Markdown
 *
 *  Markdown processing in Javascript done right. We have very particular views
 *  on what constitutes 'right' which include:
 *
 *  - produces well-formed HTML (this means that em and strong nesting is
 *    important)
 *
 *  - has an intermediate representation to allow processing of parsed data (We
 *    in fact have two, both as [JsonML]: a markdown tree and an HTML tree).
 *
 *  - is easily extensible to add new dialects without having to rewrite the
 *    entire parsing mechanics
 *
 *  - has a good test suite
 *
 *  This implementation fulfills all of these (except that the test suite could
 *  do with expanding to automatically run all the fixtures from other Markdown
 *  implementations.)
 *
 *  ##### Intermediate Representation
 *
 *  *TODO* Talk about this :) Its JsonML, but document the node names we use.
 *
 *  [JsonML]: http://jsonml.org/ "JSON Markup Language"
 **/
var Markdown = expose.Markdown = function(dialect) {
  switch (typeof dialect) {
    case "undefined":
      this.dialect = Markdown.dialects.Gruber;
      break;
    case "object":
      this.dialect = dialect;
      break;
    default:
      if ( dialect in Markdown.dialects ) {
        this.dialect = Markdown.dialects[dialect];
      }
      else {
        throw new Error("Unknown Markdown dialect '" + String(dialect) + "'");
      }
      break;
  }
  this.em_state = [];
  this.strong_state = [];
  this.debug_indent = "";
};

/**
 *  parse( markdown, [dialect] ) -> JsonML
 *  - markdown (String): markdown string to parse
 *  - dialect (String | Dialect): the dialect to use, defaults to gruber
 *
 *  Parse `markdown` and return a markdown document as a Markdown.JsonML tree.
 **/
expose.parse = function( source, dialect ) {
  // dialect will default if undefined
  var md = new Markdown( dialect );
  return md.toTree( source );
};

/**
 *  toHTML( markdown, [dialect]  ) -> String
 *  toHTML( md_tree ) -> String
 *  - markdown (String): markdown string to parse
 *  - md_tree (Markdown.JsonML): parsed markdown tree
 *
 *  Take markdown (either as a string or as a JsonML tree) and run it through
 *  [[toHTMLTree]] then turn it into a well-formated HTML fragment.
 **/
expose.toHTML = function toHTML( source , dialect , options ) {
  var input = expose.toHTMLTree( source , dialect , options );

  return expose.renderJsonML( input );
};

/**
 *  toHTMLTree( markdown, [dialect] ) -> JsonML
 *  toHTMLTree( md_tree ) -> JsonML
 *  - markdown (String): markdown string to parse
 *  - dialect (String | Dialect): the dialect to use, defaults to gruber
 *  - md_tree (Markdown.JsonML): parsed markdown tree
 *
 *  Turn markdown into HTML, represented as a JsonML tree. If a string is given
 *  to this function, it is first parsed into a markdown tree by calling
 *  [[parse]].
 **/
expose.toHTMLTree = function toHTMLTree( input, dialect , options ) {
  // convert string input to an MD tree
  if ( typeof input ==="string" ) input = this.parse( input, dialect );

  // Now convert the MD tree to an HTML tree

  // remove references from the tree
  var attrs = extract_attr( input ),
      refs = {};

  if ( attrs && attrs.references ) {
    refs = attrs.references;
  }

  var html = convert_tree_to_html( input, refs , options );
  merge_text_nodes( html );
  return html;
};

// For Spidermonkey based engines
function mk_block_toSource() {
  return "Markdown.mk_block( " +
          uneval(this.toString()) +
          ", " +
          uneval(this.trailing) +
          ", " +
          uneval(this.lineNumber) +
          " )";
}

// node
function mk_block_inspect() {
  var util = require("util");
  return "Markdown.mk_block( " +
          util.inspect(this.toString()) +
          ", " +
          util.inspect(this.trailing) +
          ", " +
          util.inspect(this.lineNumber) +
          " )";

}

var mk_block = Markdown.mk_block = function(block, trail, line) {
  // Be helpful for default case in tests.
  if ( arguments.length == 1 ) trail = "\n\n";

  var s = new String(block);
  s.trailing = trail;
  // To make it clear its not just a string
  s.inspect = mk_block_inspect;
  s.toSource = mk_block_toSource;

  if ( line != undefined )
    s.lineNumber = line;

  return s;
};

function count_lines( str ) {
  var n = 0, i = -1;
  while ( ( i = str.indexOf("\n", i + 1) ) !== -1 ) n++;
  return n;
}

// Internal - split source into rough blocks
Markdown.prototype.split_blocks = function splitBlocks( input, startLine ) {
  input = input.replace(/(\r\n|\n|\r)/g, "\n");
  // [\s\S] matches _anything_ (newline or space)
  // [^] is equivalent but doesn't work in IEs.
  var re = /([\s\S]+?)($|\n#|\n(?:\s*\n|$)+)/g,
      blocks = [],
      m;

  var line_no = 1;

  if ( ( m = /^(\s*\n)/.exec(input) ) != null ) {
    // skip (but count) leading blank lines
    line_no += count_lines( m[0] );
    re.lastIndex = m[0].length;
  }

  while ( ( m = re.exec(input) ) !== null ) {
    if (m[2] == "\n#") {
      m[2] = "\n";
      re.lastIndex--;
    }
    blocks.push( mk_block( m[1], m[2], line_no ) );
    line_no += count_lines( m[0] );
  }

  return blocks;
};

/**
 *  Markdown#processBlock( block, next ) -> undefined | [ JsonML, ... ]
 *  - block (String): the block to process
 *  - next (Array): the following blocks
 *
 * Process `block` and return an array of JsonML nodes representing `block`.
 *
 * It does this by asking each block level function in the dialect to process
 * the block until one can. Succesful handling is indicated by returning an
 * array (with zero or more JsonML nodes), failure by a false value.
 *
 * Blocks handlers are responsible for calling [[Markdown#processInline]]
 * themselves as appropriate.
 *
 * If the blocks were split incorrectly or adjacent blocks need collapsing you
 * can adjust `next` in place using shift/splice etc.
 *
 * If any of this default behaviour is not right for the dialect, you can
 * define a `__call__` method on the dialect that will get invoked to handle
 * the block processing.
 */
Markdown.prototype.processBlock = function processBlock( block, next ) {
  var cbs = this.dialect.block,
      ord = cbs.__order__;

  if ( "__call__" in cbs ) {
    return cbs.__call__.call(this, block, next);
  }

  for ( var i = 0; i < ord.length; i++ ) {
    //D:this.debug( "Testing", ord[i] );
    var res = cbs[ ord[i] ].call( this, block, next );
    if ( res ) {
      //D:this.debug("  matched");
      if ( !isArray(res) || ( res.length > 0 && !( isArray(res[0]) ) ) )
        this.debug(ord[i], "didn't return a proper array");
      //D:this.debug( "" );
      return res;
    }
  }

  // Uhoh! no match! Should we throw an error?
  return [];
};

Markdown.prototype.processInline = function processInline( block ) {
  return this.dialect.inline.__call__.call( this, String( block ) );
};

/**
 *  Markdown#toTree( source ) -> JsonML
 *  - source (String): markdown source to parse
 *
 *  Parse `source` into a JsonML tree representing the markdown document.
 **/
// custom_tree means set this.tree to `custom_tree` and restore old value on return
Markdown.prototype.toTree = function toTree( source, custom_root ) {
  var blocks = source instanceof Array ? source : this.split_blocks( source );

  // Make tree a member variable so its easier to mess with in extensions
  var old_tree = this.tree;
  try {
    this.tree = custom_root || this.tree || [ "markdown" ];

    blocks:
    while ( blocks.length ) {
      var b = this.processBlock( blocks.shift(), blocks );

      // Reference blocks and the like won't return any content
      if ( !b.length ) continue blocks;

      this.tree.push.apply( this.tree, b );
    }
    return this.tree;
  }
  finally {
    if ( custom_root ) {
      this.tree = old_tree;
    }
  }
};

// Noop by default
Markdown.prototype.debug = function () {
  var args = Array.prototype.slice.call( arguments);
  args.unshift(this.debug_indent);
  if ( typeof print !== "undefined" )
      print.apply( print, args );
  if ( typeof console !== "undefined" && typeof console.log !== "undefined" )
      console.log.apply( null, args );
}

Markdown.prototype.loop_re_over_block = function( re, block, cb ) {
  // Dont use /g regexps with this
  var m,
      b = block.valueOf();

  while ( b.length && (m = re.exec(b) ) != null ) {
    b = b.substr( m[0].length );
    cb.call(this, m);
  }
  return b;
};

/**
 * Markdown.dialects
 *
 * Namespace of built-in dialects.
 **/
Markdown.dialects = {};

/**
 * Markdown.dialects.Gruber
 *
 * The default dialect that follows the rules set out by John Gruber's
 * markdown.pl as closely as possible. Well actually we follow the behaviour of
 * that script which in some places is not exactly what the syntax web page
 * says.
 **/
Markdown.dialects.Gruber = {
  block: {
    atxHeader: function atxHeader( block, next ) {
      var m = block.match( /^(#{1,6})\s*(.*?)\s*#*\s*(?:\n|$)/ );

      if ( !m ) return undefined;

      var header = [ "header", { level: m[ 1 ].length } ];
      Array.prototype.push.apply(header, this.processInline(m[ 2 ]));

      if ( m[0].length < block.length )
        next.unshift( mk_block( block.substr( m[0].length ), block.trailing, block.lineNumber + 2 ) );

      return [ header ];
    },

    setextHeader: function setextHeader( block, next ) {
      var m = block.match( /^(.*)\n([-=])\2\2+(?:\n|$)/ );

      if ( !m ) return undefined;

      var level = ( m[ 2 ] === "=" ) ? 1 : 2;
      var header = [ "header", { level : level }, m[ 1 ] ];

      if ( m[0].length < block.length )
        next.unshift( mk_block( block.substr( m[0].length ), block.trailing, block.lineNumber + 2 ) );

      return [ header ];
    },

    code: function code( block, next ) {
      // |    Foo
      // |bar
      // should be a code block followed by a paragraph. Fun
      //
      // There might also be adjacent code block to merge.

      var ret = [],
          re = /^(?: {0,3}\t| {4})(.*)\n?/,
          lines;

      // 4 spaces + content
      if ( !block.match( re ) ) return undefined;

      block_search:
      do {
        // Now pull out the rest of the lines
        var b = this.loop_re_over_block(
                  re, block.valueOf(), function( m ) { ret.push( m[1] ); } );

        if ( b.length ) {
          // Case alluded to in first comment. push it back on as a new block
          next.unshift( mk_block(b, block.trailing) );
          break block_search;
        }
        else if ( next.length ) {
          // Check the next block - it might be code too
          if ( !next[0].match( re ) ) break block_search;

          // Pull how how many blanks lines follow - minus two to account for .join
          ret.push ( block.trailing.replace(/[^\n]/g, "").substring(2) );

          block = next.shift();
        }
        else {
          break block_search;
        }
      } while ( true );

      return [ [ "code_block", ret.join("\n") ] ];
    },

    horizRule: function horizRule( block, next ) {
      // this needs to find any hr in the block to handle abutting blocks
      var m = block.match( /^(?:([\s\S]*?)\n)?[ \t]*([-_*])(?:[ \t]*\2){2,}[ \t]*(?:\n([\s\S]*))?$/ );

      if ( !m ) {
        return undefined;
      }

      var jsonml = [ [ "hr" ] ];

      // if there's a leading abutting block, process it
      if ( m[ 1 ] ) {
        jsonml.unshift.apply( jsonml, this.processBlock( m[ 1 ], [] ) );
      }

      // if there's a trailing abutting block, stick it into next
      if ( m[ 3 ] ) {
        next.unshift( mk_block( m[ 3 ] ) );
      }

      return jsonml;
    },

    // There are two types of lists. Tight and loose. Tight lists have no whitespace
    // between the items (and result in text just in the <li>) and loose lists,
    // which have an empty line between list items, resulting in (one or more)
    // paragraphs inside the <li>.
    //
    // There are all sorts weird edge cases about the original markdown.pl's
    // handling of lists:
    //
    // * Nested lists are supposed to be indented by four chars per level. But
    //   if they aren't, you can get a nested list by indenting by less than
    //   four so long as the indent doesn't match an indent of an existing list
    //   item in the 'nest stack'.
    //
    // * The type of the list (bullet or number) is controlled just by the
    //    first item at the indent. Subsequent changes are ignored unless they
    //    are for nested lists
    //
    lists: (function( ) {
      // Use a closure to hide a few variables.
      var any_list = "[*+-]|\\d+\\.",
          bullet_list = /[*+-]/,
          number_list = /\d+\./,
          // Capture leading indent as it matters for determining nested lists.
          is_list_re = new RegExp( "^( {0,3})(" + any_list + ")[ \t]+" ),
          indent_re = "(?: {0,3}\\t| {4})";

      // TODO: Cache this regexp for certain depths.
      // Create a regexp suitable for matching an li for a given stack depth
      function regex_for_depth( depth ) {

        return new RegExp(
          // m[1] = indent, m[2] = list_type
          "(?:^(" + indent_re + "{0," + depth + "} {0,3})(" + any_list + ")\\s+)|" +
          // m[3] = cont
          "(^" + indent_re + "{0," + (depth-1) + "}[ ]{0,4})"
        );
      }
      function expand_tab( input ) {
        return input.replace( / {0,3}\t/g, "    " );
      }

      // Add inline content `inline` to `li`. inline comes from processInline
      // so is an array of content
      function add(li, loose, inline, nl) {
        if ( loose ) {
          li.push( [ "para" ].concat(inline) );
          return;
        }
        // Hmmm, should this be any block level element or just paras?
        var add_to = li[li.length -1] instanceof Array && li[li.length - 1][0] == "para"
                   ? li[li.length -1]
                   : li;

        // If there is already some content in this list, add the new line in
        if ( nl && li.length > 1 ) inline.unshift(nl);

        for ( var i = 0; i < inline.length; i++ ) {
          var what = inline[i],
              is_str = typeof what == "string";
          if ( is_str && add_to.length > 1 && typeof add_to[add_to.length-1] == "string" ) {
            add_to[ add_to.length-1 ] += what;
          }
          else {
            add_to.push( what );
          }
        }
      }

      // contained means have an indent greater than the current one. On
      // *every* line in the block
      function get_contained_blocks( depth, blocks ) {

        var re = new RegExp( "^(" + indent_re + "{" + depth + "}.*?\\n?)*$" ),
            replace = new RegExp("^" + indent_re + "{" + depth + "}", "gm"),
            ret = [];

        while ( blocks.length > 0 ) {
          if ( re.exec( blocks[0] ) ) {
            var b = blocks.shift(),
                // Now remove that indent
                x = b.replace( replace, "");

            ret.push( mk_block( x, b.trailing, b.lineNumber ) );
          }
          else {
            break;
          }
        }
        return ret;
      }

      // passed to stack.forEach to turn list items up the stack into paras
      function paragraphify(s, i, stack) {
        var list = s.list;
        var last_li = list[list.length-1];

        if ( last_li[1] instanceof Array && last_li[1][0] == "para" ) {
          return;
        }
        if ( i + 1 == stack.length ) {
          // Last stack frame
          // Keep the same array, but replace the contents
          last_li.push( ["para"].concat( last_li.splice(1, last_li.length - 1) ) );
        }
        else {
          var sublist = last_li.pop();
          last_li.push( ["para"].concat( last_li.splice(1, last_li.length - 1) ), sublist );
        }
      }

      // The matcher function
      return function( block, next ) {
        var m = block.match( is_list_re );
        if ( !m ) return undefined;

        function make_list( m ) {
          var list = bullet_list.exec( m[2] )
                   ? ["bulletlist"]
                   : ["numberlist"];

          stack.push( { list: list, indent: m[1] } );
          return list;
        }


        var stack = [], // Stack of lists for nesting.
            list = make_list( m ),
            last_li,
            loose = false,
            ret = [ stack[0].list ],
            i;

        // Loop to search over block looking for inner block elements and loose lists
        loose_search:
        while ( true ) {
          // Split into lines preserving new lines at end of line
          var lines = block.split( /(?=\n)/ );

          // We have to grab all lines for a li and call processInline on them
          // once as there are some inline things that can span lines.
          var li_accumulate = "";

          // Loop over the lines in this block looking for tight lists.
          tight_search:
          for ( var line_no = 0; line_no < lines.length; line_no++ ) {
            var nl = "",
                l = lines[line_no].replace(/^\n/, function(n) { nl = n; return ""; });

            // TODO: really should cache this
            var line_re = regex_for_depth( stack.length );

            m = l.match( line_re );
            //print( "line:", uneval(l), "\nline match:", uneval(m) );

            // We have a list item
            if ( m[1] !== undefined ) {
              // Process the previous list item, if any
              if ( li_accumulate.length ) {
                add( last_li, loose, this.processInline( li_accumulate ), nl );
                // Loose mode will have been dealt with. Reset it
                loose = false;
                li_accumulate = "";
              }

              m[1] = expand_tab( m[1] );
              var wanted_depth = Math.floor(m[1].length/4)+1;
              //print( "want:", wanted_depth, "stack:", stack.length);
              if ( wanted_depth > stack.length ) {
                // Deep enough for a nested list outright
                //print ( "new nested list" );
                list = make_list( m );
                last_li.push( list );
                last_li = list[1] = [ "listitem" ];
              }
              else {
                // We aren't deep enough to be strictly a new level. This is
                // where Md.pl goes nuts. If the indent matches a level in the
                // stack, put it there, else put it one deeper then the
                // wanted_depth deserves.
                var found = false;
                for ( i = 0; i < stack.length; i++ ) {
                  if ( stack[ i ].indent != m[1] ) continue;
                  list = stack[ i ].list;
                  stack.splice( i+1, stack.length - (i+1) );
                  found = true;
                  break;
                }

                if (!found) {
                  //print("not found. l:", uneval(l));
                  wanted_depth++;
                  if ( wanted_depth <= stack.length ) {
                    stack.splice(wanted_depth, stack.length - wanted_depth);
                    //print("Desired depth now", wanted_depth, "stack:", stack.length);
                    list = stack[wanted_depth-1].list;
                    //print("list:", uneval(list) );
                  }
                  else {
                    //print ("made new stack for messy indent");
                    list = make_list(m);
                    last_li.push(list);
                  }
                }

                //print( uneval(list), "last", list === stack[stack.length-1].list );
                last_li = [ "listitem" ];
                list.push(last_li);
              } // end depth of shenegains
              nl = "";
            }

            // Add content
            if ( l.length > m[0].length ) {
              li_accumulate += nl + l.substr( m[0].length );
            }
          } // tight_search

          if ( li_accumulate.length ) {
            add( last_li, loose, this.processInline( li_accumulate ), nl );
            // Loose mode will have been dealt with. Reset it
            loose = false;
            li_accumulate = "";
          }

          // Look at the next block - we might have a loose list. Or an extra
          // paragraph for the current li
          var contained = get_contained_blocks( stack.length, next );

          // Deal with code blocks or properly nested lists
          if ( contained.length > 0 ) {
            // Make sure all listitems up the stack are paragraphs
            forEach( stack, paragraphify, this);

            last_li.push.apply( last_li, this.toTree( contained, [] ) );
          }

          var next_block = next[0] && next[0].valueOf() || "";

          if ( next_block.match(is_list_re) || next_block.match( /^ / ) ) {
            block = next.shift();

            // Check for an HR following a list: features/lists/hr_abutting
            var hr = this.dialect.block.horizRule( block, next );

            if ( hr ) {
              ret.push.apply(ret, hr);
              break;
            }

            // Make sure all listitems up the stack are paragraphs
            forEach( stack, paragraphify, this);

            loose = true;
            continue loose_search;
          }
          break;
        } // loose_search

        return ret;
      };
    })(),

    blockquote: function blockquote( block, next ) {
      if ( !block.match( /^>/m ) )
        return undefined;

      var jsonml = [];

      // separate out the leading abutting block, if any. I.e. in this case:
      //
      //  a
      //  > b
      //
      if ( block[ 0 ] != ">" ) {
        var lines = block.split( /\n/ ),
            prev = [],
            line_no = block.lineNumber;

        // keep shifting lines until you find a crotchet
        while ( lines.length && lines[ 0 ][ 0 ] != ">" ) {
            prev.push( lines.shift() );
            line_no++;
        }

        var abutting = mk_block( prev.join( "\n" ), "\n", block.lineNumber );
        jsonml.push.apply( jsonml, this.processBlock( abutting, [] ) );
        // reassemble new block of just block quotes!
        block = mk_block( lines.join( "\n" ), block.trailing, line_no );
      }


      // if the next block is also a blockquote merge it in
      while ( next.length && next[ 0 ][ 0 ] == ">" ) {
        var b = next.shift();
        block = mk_block( block + block.trailing + b, b.trailing, block.lineNumber );
      }

      // Strip off the leading "> " and re-process as a block.
      var input = block.replace( /^> ?/gm, "" ),
          old_tree = this.tree,
          processedBlock = this.toTree( input, [ "blockquote" ] ),
          attr = extract_attr( processedBlock );

      // If any link references were found get rid of them
      if ( attr && attr.references ) {
        delete attr.references;
        // And then remove the attribute object if it's empty
        if ( isEmpty( attr ) ) {
          processedBlock.splice( 1, 1 );
        }
      }

      jsonml.push( processedBlock );
      return jsonml;
    },

    referenceDefn: function referenceDefn( block, next) {
      var re = /^\s*\[(.*?)\]:\s*(\S+)(?:\s+(?:(['"])(.*?)\3|\((.*?)\)))?\n?/;
      // interesting matches are [ , ref_id, url, , title, title ]

      if ( !block.match(re) )
        return undefined;

      // make an attribute node if it doesn't exist
      if ( !extract_attr( this.tree ) ) {
        this.tree.splice( 1, 0, {} );
      }

      var attrs = extract_attr( this.tree );

      // make a references hash if it doesn't exist
      if ( attrs.references === undefined ) {
        attrs.references = {};
      }

      var b = this.loop_re_over_block(re, block, function( m ) {

        if ( m[2] && m[2][0] == "<" && m[2][m[2].length-1] == ">" )
          m[2] = m[2].substring( 1, m[2].length - 1 );

        var ref = attrs.references[ m[1].toLowerCase() ] = {
          href: m[2]
        };

        if ( m[4] !== undefined )
          ref.title = m[4];
        else if ( m[5] !== undefined )
          ref.title = m[5];

      } );

      if ( b.length )
        next.unshift( mk_block( b, block.trailing ) );

      return [];
    },

    para: function para( block, next ) {
      // everything's a para!
      return [ ["para"].concat( this.processInline( block ) ) ];
    }
  }
};

Markdown.dialects.Gruber.inline = {

    __oneElement__: function oneElement( text, patterns_or_re, previous_nodes ) {
      var m,
          res,
          lastIndex = 0;

      patterns_or_re = patterns_or_re || this.dialect.inline.__patterns__;
      var re = new RegExp( "([\\s\\S]*?)(" + (patterns_or_re.source || patterns_or_re) + ")" );

      m = re.exec( text );
      if (!m) {
        // Just boring text
        return [ text.length, text ];
      }
      else if ( m[1] ) {
        // Some un-interesting text matched. Return that first
        return [ m[1].length, m[1] ];
      }

      var res;
      if ( m[2] in this.dialect.inline ) {
        res = this.dialect.inline[ m[2] ].call(
                  this,
                  text.substr( m.index ), m, previous_nodes || [] );
      }
      // Default for now to make dev easier. just slurp special and output it.
      res = res || [ m[2].length, m[2] ];
      return res;
    },

    __call__: function inline( text, patterns ) {

      var out = [],
          res;

      function add(x) {
        //D:self.debug("  adding output", uneval(x));
        if ( typeof x == "string" && typeof out[out.length-1] == "string" )
          out[ out.length-1 ] += x;
        else
          out.push(x);
      }

      while ( text.length > 0 ) {
        res = this.dialect.inline.__oneElement__.call(this, text, patterns, out );
        text = text.substr( res.shift() );
        forEach(res, add )
      }

      return out;
    },

    // These characters are intersting elsewhere, so have rules for them so that
    // chunks of plain text blocks don't include them
    "]": function () {},
    "}": function () {},

    __escape__ : /^\\[\\`\*_{}\[\]()#\+.!\-]/,

    "\\": function escaped( text ) {
      // [ length of input processed, node/children to add... ]
      // Only esacape: \ ` * _ { } [ ] ( ) # * + - . !
      if ( this.dialect.inline.__escape__.exec( text ) )
        return [ 2, text.charAt( 1 ) ];
      else
        // Not an esacpe
        return [ 1, "\\" ];
    },

    "![": function image( text ) {

      // Unlike images, alt text is plain text only. no other elements are
      // allowed in there

      // ![Alt text](/path/to/img.jpg "Optional title")
      //      1          2            3       4         <--- captures
      var m = text.match( /^!\[(.*?)\][ \t]*\([ \t]*([^")]*?)(?:[ \t]+(["'])(.*?)\3)?[ \t]*\)/ );

      if ( m ) {
        if ( m[2] && m[2][0] == "<" && m[2][m[2].length-1] == ">" )
          m[2] = m[2].substring( 1, m[2].length - 1 );

        m[2] = this.dialect.inline.__call__.call( this, m[2], /\\/ )[0];

        var attrs = { alt: m[1], href: m[2] || "" };
        if ( m[4] !== undefined)
          attrs.title = m[4];

        return [ m[0].length, [ "img", attrs ] ];
      }

      // ![Alt text][id]
      m = text.match( /^!\[(.*?)\][ \t]*\[(.*?)\]/ );

      if ( m ) {
        // We can't check if the reference is known here as it likely wont be
        // found till after. Check it in md tree->hmtl tree conversion
        return [ m[0].length, [ "img_ref", { alt: m[1], ref: m[2].toLowerCase(), original: m[0] } ] ];
      }

      // Just consume the '!['
      return [ 2, "![" ];
    },

    "[": function link( text ) {

      var orig = String(text);
      // Inline content is possible inside `link text`
      var res = Markdown.DialectHelpers.inline_until_char.call( this, text.substr(1), "]" );

      // No closing ']' found. Just consume the [
      if ( !res ) return [ 1, "[" ];

      var consumed = 1 + res[ 0 ],
          children = res[ 1 ],
          link,
          attrs;

      // At this point the first [...] has been parsed. See what follows to find
      // out which kind of link we are (reference or direct url)
      text = text.substr( consumed );

      // [link text](/path/to/img.jpg "Optional title")
      //                 1            2       3         <--- captures
      // This will capture up to the last paren in the block. We then pull
      // back based on if there a matching ones in the url
      //    ([here](/url/(test))
      // The parens have to be balanced
      var m = text.match( /^\s*\([ \t]*([^"']*)(?:[ \t]+(["'])(.*?)\2)?[ \t]*\)/ );
      if ( m ) {
        var url = m[1];
        consumed += m[0].length;

        if ( url && url[0] == "<" && url[url.length-1] == ">" )
          url = url.substring( 1, url.length - 1 );

        // If there is a title we don't have to worry about parens in the url
        if ( !m[3] ) {
          var open_parens = 1; // One open that isn't in the capture
          for ( var len = 0; len < url.length; len++ ) {
            switch ( url[len] ) {
            case "(":
              open_parens++;
              break;
            case ")":
              if ( --open_parens == 0) {
                consumed -= url.length - len;
                url = url.substring(0, len);
              }
              break;
            }
          }
        }

        // Process escapes only
        url = this.dialect.inline.__call__.call( this, url, /\\/ )[0];

        attrs = { href: url || "" };
        if ( m[3] !== undefined)
          attrs.title = m[3];

        link = [ "link", attrs ].concat( children );
        return [ consumed, link ];
      }

      // [Alt text][id]
      // [Alt text] [id]
      m = text.match( /^\s*\[(.*?)\]/ );

      if ( m ) {

        consumed += m[ 0 ].length;

        // [links][] uses links as its reference
        attrs = { ref: ( m[ 1 ] || String(children) ).toLowerCase(),  original: orig.substr( 0, consumed ) };

        link = [ "link_ref", attrs ].concat( children );

        // We can't check if the reference is known here as it likely wont be
        // found till after. Check it in md tree->hmtl tree conversion.
        // Store the original so that conversion can revert if the ref isn't found.
        return [ consumed, link ];
      }

      // [id]
      // Only if id is plain (no formatting.)
      if ( children.length == 1 && typeof children[0] == "string" ) {

        attrs = { ref: children[0].toLowerCase(),  original: orig.substr( 0, consumed ) };
        link = [ "link_ref", attrs, children[0] ];
        return [ consumed, link ];
      }

      // Just consume the "["
      return [ 1, "[" ];
    },


    "<": function autoLink( text ) {
      var m;

      if ( ( m = text.match( /^<(?:((https?|ftp|mailto):[^>]+)|(.*?@.*?\.[a-zA-Z]+))>/ ) ) != null ) {
        if ( m[3] ) {
          return [ m[0].length, [ "link", { href: "mailto:" + m[3] }, m[3] ] ];

        }
        else if ( m[2] == "mailto" ) {
          return [ m[0].length, [ "link", { href: m[1] }, m[1].substr("mailto:".length ) ] ];
        }
        else
          return [ m[0].length, [ "link", { href: m[1] }, m[1] ] ];
      }

      return [ 1, "<" ];
    },

    "`": function inlineCode( text ) {
      // Inline code block. as many backticks as you like to start it
      // Always skip over the opening ticks.
      var m = text.match( /(`+)(([\s\S]*?)\1)/ );

      if ( m && m[2] )
        return [ m[1].length + m[2].length, [ "inlinecode", m[3] ] ];
      else {
        // TODO: No matching end code found - warn!
        return [ 1, "`" ];
      }
    },

    "  \n": function lineBreak( text ) {
      return [ 3, [ "linebreak" ] ];
    }

};

// Meta Helper/generator method for em and strong handling
function strong_em( tag, md ) {

  var state_slot = tag + "_state",
      other_slot = tag == "strong" ? "em_state" : "strong_state";

  function CloseTag(len) {
    this.len_after = len;
    this.name = "close_" + md;
  }

  return function ( text, orig_match ) {

    if ( this[state_slot][0] == md ) {
      // Most recent em is of this type
      //D:this.debug("closing", md);
      this[state_slot].shift();

      // "Consume" everything to go back to the recrusion in the else-block below
      return[ text.length, new CloseTag(text.length-md.length) ];
    }
    else {
      // Store a clone of the em/strong states
      var other = this[other_slot].slice(),
          state = this[state_slot].slice();

      this[state_slot].unshift(md);

      //D:this.debug_indent += "  ";

      // Recurse
      var res = this.processInline( text.substr( md.length ) );
      //D:this.debug_indent = this.debug_indent.substr(2);

      var last = res[res.length - 1];

      //D:this.debug("processInline from", tag + ": ", uneval( res ) );

      var check = this[state_slot].shift();
      if ( last instanceof CloseTag ) {
        res.pop();
        // We matched! Huzzah.
        var consumed = text.length - last.len_after;
        return [ consumed, [ tag ].concat(res) ];
      }
      else {
        // Restore the state of the other kind. We might have mistakenly closed it.
        this[other_slot] = other;
        this[state_slot] = state;

        // We can't reuse the processed result as it could have wrong parsing contexts in it.
        return [ md.length, md ];
      }
    }
  }; // End returned function
}

Markdown.dialects.Gruber.inline["**"] = strong_em("strong", "**");
Markdown.dialects.Gruber.inline["__"] = strong_em("strong", "__");
Markdown.dialects.Gruber.inline["*"]  = strong_em("em", "*");
Markdown.dialects.Gruber.inline["_"]  = strong_em("em", "_");


// Build default order from insertion order.
Markdown.buildBlockOrder = function(d) {
  var ord = [];
  for ( var i in d ) {
    if ( i == "__order__" || i == "__call__" ) continue;
    ord.push( i );
  }
  d.__order__ = ord;
};

// Build patterns for inline matcher
Markdown.buildInlinePatterns = function(d) {
  var patterns = [];

  for ( var i in d ) {
    // __foo__ is reserved and not a pattern
    if ( i.match( /^__.*__$/) ) continue;
    var l = i.replace( /([\\.*+?|()\[\]{}])/g, "\\$1" )
             .replace( /\n/, "\\n" );
    patterns.push( i.length == 1 ? l : "(?:" + l + ")" );
  }

  patterns = patterns.join("|");
  d.__patterns__ = patterns;
  //print("patterns:", uneval( patterns ) );

  var fn = d.__call__;
  d.__call__ = function(text, pattern) {
    if ( pattern != undefined ) {
      return fn.call(this, text, pattern);
    }
    else
    {
      return fn.call(this, text, patterns);
    }
  };
};

Markdown.DialectHelpers = {};
Markdown.DialectHelpers.inline_until_char = function( text, want ) {
  var consumed = 0,
      nodes = [];

  while ( true ) {
    if ( text.charAt( consumed ) == want ) {
      // Found the character we were looking for
      consumed++;
      return [ consumed, nodes ];
    }

    if ( consumed >= text.length ) {
      // No closing char found. Abort.
      return null;
    }

    var res = this.dialect.inline.__oneElement__.call(this, text.substr( consumed ) );
    consumed += res[ 0 ];
    // Add any returned nodes.
    nodes.push.apply( nodes, res.slice( 1 ) );
  }
}

// Helper function to make sub-classing a dialect easier
Markdown.subclassDialect = function( d ) {
  function Block() {}
  Block.prototype = d.block;
  function Inline() {}
  Inline.prototype = d.inline;

  return { block: new Block(), inline: new Inline() };
};

Markdown.buildBlockOrder ( Markdown.dialects.Gruber.block );
Markdown.buildInlinePatterns( Markdown.dialects.Gruber.inline );

Markdown.dialects.Maruku = Markdown.subclassDialect( Markdown.dialects.Gruber );

Markdown.dialects.Maruku.processMetaHash = function processMetaHash( meta_string ) {
  var meta = split_meta_hash( meta_string ),
      attr = {};

  for ( var i = 0; i < meta.length; ++i ) {
    // id: #foo
    if ( /^#/.test( meta[ i ] ) ) {
      attr.id = meta[ i ].substring( 1 );
    }
    // class: .foo
    else if ( /^\./.test( meta[ i ] ) ) {
      // if class already exists, append the new one
      if ( attr["class"] ) {
        attr["class"] = attr["class"] + meta[ i ].replace( /./, " " );
      }
      else {
        attr["class"] = meta[ i ].substring( 1 );
      }
    }
    // attribute: foo=bar
    else if ( /\=/.test( meta[ i ] ) ) {
      var s = meta[ i ].split( /\=/ );
      attr[ s[ 0 ] ] = s[ 1 ];
    }
  }

  return attr;
}

function split_meta_hash( meta_string ) {
  var meta = meta_string.split( "" ),
      parts = [ "" ],
      in_quotes = false;

  while ( meta.length ) {
    var letter = meta.shift();
    switch ( letter ) {
      case " " :
        // if we're in a quoted section, keep it
        if ( in_quotes ) {
          parts[ parts.length - 1 ] += letter;
        }
        // otherwise make a new part
        else {
          parts.push( "" );
        }
        break;
      case "'" :
      case '"' :
        // reverse the quotes and move straight on
        in_quotes = !in_quotes;
        break;
      case "\\" :
        // shift off the next letter to be used straight away.
        // it was escaped so we'll keep it whatever it is
        letter = meta.shift();
      default :
        parts[ parts.length - 1 ] += letter;
        break;
    }
  }

  return parts;
}

Markdown.dialects.Maruku.block.document_meta = function document_meta( block, next ) {
  // we're only interested in the first block
  if ( block.lineNumber > 1 ) return undefined;

  // document_meta blocks consist of one or more lines of `Key: Value\n`
  if ( ! block.match( /^(?:\w+:.*\n)*\w+:.*$/ ) ) return undefined;

  // make an attribute node if it doesn't exist
  if ( !extract_attr( this.tree ) ) {
    this.tree.splice( 1, 0, {} );
  }

  var pairs = block.split( /\n/ );
  for ( p in pairs ) {
    var m = pairs[ p ].match( /(\w+):\s*(.*)$/ ),
        key = m[ 1 ].toLowerCase(),
        value = m[ 2 ];

    this.tree[ 1 ][ key ] = value;
  }

  // document_meta produces no content!
  return [];
};

Markdown.dialects.Maruku.block.block_meta = function block_meta( block, next ) {
  // check if the last line of the block is an meta hash
  var m = block.match( /(^|\n) {0,3}\{:\s*((?:\\\}|[^\}])*)\s*\}$/ );
  if ( !m ) return undefined;

  // process the meta hash
  var attr = this.dialect.processMetaHash( m[ 2 ] );

  var hash;

  // if we matched ^ then we need to apply meta to the previous block
  if ( m[ 1 ] === "" ) {
    var node = this.tree[ this.tree.length - 1 ];
    hash = extract_attr( node );

    // if the node is a string (rather than JsonML), bail
    if ( typeof node === "string" ) return undefined;

    // create the attribute hash if it doesn't exist
    if ( !hash ) {
      hash = {};
      node.splice( 1, 0, hash );
    }

    // add the attributes in
    for ( a in attr ) {
      hash[ a ] = attr[ a ];
    }

    // return nothing so the meta hash is removed
    return [];
  }

  // pull the meta hash off the block and process what's left
  var b = block.replace( /\n.*$/, "" ),
      result = this.processBlock( b, [] );

  // get or make the attributes hash
  hash = extract_attr( result[ 0 ] );
  if ( !hash ) {
    hash = {};
    result[ 0 ].splice( 1, 0, hash );
  }

  // attach the attributes to the block
  for ( a in attr ) {
    hash[ a ] = attr[ a ];
  }

  return result;
};

Markdown.dialects.Maruku.block.definition_list = function definition_list( block, next ) {
  // one or more terms followed by one or more definitions, in a single block
  var tight = /^((?:[^\s:].*\n)+):\s+([\s\S]+)$/,
      list = [ "dl" ],
      i, m;

  // see if we're dealing with a tight or loose block
  if ( ( m = block.match( tight ) ) ) {
    // pull subsequent tight DL blocks out of `next`
    var blocks = [ block ];
    while ( next.length && tight.exec( next[ 0 ] ) ) {
      blocks.push( next.shift() );
    }

    for ( var b = 0; b < blocks.length; ++b ) {
      var m = blocks[ b ].match( tight ),
          terms = m[ 1 ].replace( /\n$/, "" ).split( /\n/ ),
          defns = m[ 2 ].split( /\n:\s+/ );

      // print( uneval( m ) );

      for ( i = 0; i < terms.length; ++i ) {
        list.push( [ "dt", terms[ i ] ] );
      }

      for ( i = 0; i < defns.length; ++i ) {
        // run inline processing over the definition
        list.push( [ "dd" ].concat( this.processInline( defns[ i ].replace( /(\n)\s+/, "$1" ) ) ) );
      }
    }
  }
  else {
    return undefined;
  }

  return [ list ];
};

// splits on unescaped instances of @ch. If @ch is not a character the result
// can be unpredictable

Markdown.dialects.Maruku.block.table = function table (block, next) {

    var _split_on_unescaped = function(s, ch) {
        ch = ch || '\\s';
        if (ch.match(/^[\\|\[\]{}?*.+^$]$/)) { ch = '\\' + ch; }
        var res = [ ],
            r = new RegExp('^((?:\\\\.|[^\\\\' + ch + '])*)' + ch + '(.*)'),
            m;
        while(m = s.match(r)) {
            res.push(m[1]);
            s = m[2];
        }
        res.push(s);
        return res;
    }

    var leading_pipe = /^ {0,3}\|(.+)\n {0,3}\|\s*([\-:]+[\-| :]*)\n((?:\s*\|.*(?:\n|$))*)(?=\n|$)/,
        // find at least an unescaped pipe in each line
        no_leading_pipe = /^ {0,3}(\S(?:\\.|[^\\|])*\|.*)\n {0,3}([\-:]+\s*\|[\-| :]*)\n((?:(?:\\.|[^\\|])*\|.*(?:\n|$))*)(?=\n|$)/,
        i, m;
    if (m = block.match(leading_pipe)) {
        // remove leading pipes in contents
        // (header and horizontal rule already have the leading pipe left out)
        m[3] = m[3].replace(/^\s*\|/gm, '');
    } else if (! ( m = block.match(no_leading_pipe))) {
        return undefined;
    }

    var table = [ "table", [ "thead", [ "tr" ] ], [ "tbody" ] ];

    // remove trailing pipes, then split on pipes
    // (no escaped pipes are allowed in horizontal rule)
    m[2] = m[2].replace(/\|\s*$/, '').split('|');

    // process alignment
    var html_attrs = [ ];
    forEach (m[2], function (s) {
        if (s.match(/^\s*-+:\s*$/))       html_attrs.push({align: "right"});
        else if (s.match(/^\s*:-+\s*$/))  html_attrs.push({align: "left"});
        else if (s.match(/^\s*:-+:\s*$/)) html_attrs.push({align: "center"});
        else                              html_attrs.push({});
    });

    // now for the header, avoid escaped pipes
    m[1] = _split_on_unescaped(m[1].replace(/\|\s*$/, ''), '|');
    for (i = 0; i < m[1].length; i++) {
        table[1][1].push(['th', html_attrs[i] || {}].concat(
            this.processInline(m[1][i].trim())));
    }

    // now for body contents
    forEach (m[3].replace(/\|\s*$/mg, '').split('\n'), function (row) {
        var html_row = ['tr'];
        row = _split_on_unescaped(row, '|');
        for (i = 0; i < row.length; i++) {
            html_row.push(['td', html_attrs[i] || {}].concat(this.processInline(row[i].trim())));
        }
        table[2].push(html_row);
    }, this);

    return [table];
}

Markdown.dialects.Maruku.inline[ "{:" ] = function inline_meta( text, matches, out ) {
  if ( !out.length ) {
    return [ 2, "{:" ];
  }

  // get the preceeding element
  var before = out[ out.length - 1 ];

  if ( typeof before === "string" ) {
    return [ 2, "{:" ];
  }

  // match a meta hash
  var m = text.match( /^\{:\s*((?:\\\}|[^\}])*)\s*\}/ );

  // no match, false alarm
  if ( !m ) {
    return [ 2, "{:" ];
  }

  // attach the attributes to the preceeding element
  var meta = this.dialect.processMetaHash( m[ 1 ] ),
      attr = extract_attr( before );

  if ( !attr ) {
    attr = {};
    before.splice( 1, 0, attr );
  }

  for ( var k in meta ) {
    attr[ k ] = meta[ k ];
  }

  // cut out the string and replace it with nothing
  return [ m[ 0 ].length, "" ];
};

Markdown.dialects.Maruku.inline.__escape__ = /^\\[\\`\*_{}\[\]()#\+.!\-|:]/;

Markdown.buildBlockOrder ( Markdown.dialects.Maruku.block );
Markdown.buildInlinePatterns( Markdown.dialects.Maruku.inline );

var isArray = Array.isArray || function(obj) {
  return Object.prototype.toString.call(obj) == "[object Array]";
};

var forEach;
// Don't mess with Array.prototype. Its not friendly
if ( Array.prototype.forEach ) {
  forEach = function( arr, cb, thisp ) {
    return arr.forEach( cb, thisp );
  };
}
else {
  forEach = function(arr, cb, thisp) {
    for (var i = 0; i < arr.length; i++) {
      cb.call(thisp || arr, arr[i], i, arr);
    }
  }
}

var isEmpty = function( obj ) {
  for ( var key in obj ) {
    if ( hasOwnProperty.call( obj, key ) ) {
      return false;
    }
  }

  return true;
}

function extract_attr( jsonml ) {
  return isArray(jsonml)
      && jsonml.length > 1
      && typeof jsonml[ 1 ] === "object"
      && !( isArray(jsonml[ 1 ]) )
      ? jsonml[ 1 ]
      : undefined;
}



/**
 *  renderJsonML( jsonml[, options] ) -> String
 *  - jsonml (Array): JsonML array to render to XML
 *  - options (Object): options
 *
 *  Converts the given JsonML into well-formed XML.
 *
 *  The options currently understood are:
 *
 *  - root (Boolean): wether or not the root node should be included in the
 *    output, or just its children. The default `false` is to not include the
 *    root itself.
 */
expose.renderJsonML = function( jsonml, options ) {
  options = options || {};
  // include the root element in the rendered output?
  options.root = options.root || false;

  var content = [];

  if ( options.root ) {
    content.push( render_tree( jsonml ) );
  }
  else {
    jsonml.shift(); // get rid of the tag
    if ( jsonml.length && typeof jsonml[ 0 ] === "object" && !( jsonml[ 0 ] instanceof Array ) ) {
      jsonml.shift(); // get rid of the attributes
    }

    while ( jsonml.length ) {
      content.push( render_tree( jsonml.shift() ) );
    }
  }

  return content.join( "\n\n" );
};

function escapeHTML( text ) {
  return text.replace( /&/g, "&amp;" )
             .replace( /</g, "&lt;" )
             .replace( />/g, "&gt;" )
             .replace( /"/g, "&quot;" )
             .replace( /'/g, "&#39;" );
}

function render_tree( jsonml ) {
  // basic case
  if ( typeof jsonml === "string" ) {
    return escapeHTML( jsonml );
  }

  var tag = jsonml.shift(),
      attributes = {},
      content = [];

  if ( jsonml.length && typeof jsonml[ 0 ] === "object" && !( jsonml[ 0 ] instanceof Array ) ) {
    attributes = jsonml.shift();
  }

  while ( jsonml.length ) {
    content.push( render_tree( jsonml.shift() ) );
  }

  var tag_attrs = "";
  for ( var a in attributes ) {
    tag_attrs += " " + a + '="' + escapeHTML( attributes[ a ] ) + '"';
  }

  // be careful about adding whitespace here for inline elements
  if ( tag == "img" || tag == "br" || tag == "hr" ) {
    return "<"+ tag + tag_attrs + "/>";
  }
  else {
    return "<"+ tag + tag_attrs + ">" + content.join( "" ) + "</" + tag + ">";
  }
}

function convert_tree_to_html( tree, references, options ) {
  var i;
  options = options || {};

  // shallow clone
  var jsonml = tree.slice( 0 );

  if ( typeof options.preprocessTreeNode === "function" ) {
      jsonml = options.preprocessTreeNode(jsonml, references);
  }

  // Clone attributes if they exist
  var attrs = extract_attr( jsonml );
  if ( attrs ) {
    jsonml[ 1 ] = {};
    for ( i in attrs ) {
      jsonml[ 1 ][ i ] = attrs[ i ];
    }
    attrs = jsonml[ 1 ];
  }

  // basic case
  if ( typeof jsonml === "string" ) {
    return jsonml;
  }

  // convert this node
  switch ( jsonml[ 0 ] ) {
    case "header":
      jsonml[ 0 ] = "h" + jsonml[ 1 ].level;
      delete jsonml[ 1 ].level;
      break;
    case "bulletlist":
      jsonml[ 0 ] = "ul";
      break;
    case "numberlist":
      jsonml[ 0 ] = "ol";
      break;
    case "listitem":
      jsonml[ 0 ] = "li";
      break;
    case "para":
      jsonml[ 0 ] = "p";
      break;
    case "markdown":
      jsonml[ 0 ] = "html";
      if ( attrs ) delete attrs.references;
      break;
    case "code_block":
      jsonml[ 0 ] = "pre";
      i = attrs ? 2 : 1;
      var code = [ "code" ];
      code.push.apply( code, jsonml.splice( i, jsonml.length - i ) );
      jsonml[ i ] = code;
      break;
    case "inlinecode":
      jsonml[ 0 ] = "code";
      break;
    case "img":
      jsonml[ 1 ].src = jsonml[ 1 ].href;
      delete jsonml[ 1 ].href;
      break;
    case "linebreak":
      jsonml[ 0 ] = "br";
    break;
    case "link":
      jsonml[ 0 ] = "a";
      break;
    case "link_ref":
      jsonml[ 0 ] = "a";

      // grab this ref and clean up the attribute node
      var ref = references[ attrs.ref ];

      // if the reference exists, make the link
      if ( ref ) {
        delete attrs.ref;

        // add in the href and title, if present
        attrs.href = ref.href;
        if ( ref.title ) {
          attrs.title = ref.title;
        }

        // get rid of the unneeded original text
        delete attrs.original;
      }
      // the reference doesn't exist, so revert to plain text
      else {
        return attrs.original;
      }
      break;
    case "img_ref":
      jsonml[ 0 ] = "img";

      // grab this ref and clean up the attribute node
      var ref = references[ attrs.ref ];

      // if the reference exists, make the link
      if ( ref ) {
        delete attrs.ref;

        // add in the href and title, if present
        attrs.src = ref.href;
        if ( ref.title ) {
          attrs.title = ref.title;
        }

        // get rid of the unneeded original text
        delete attrs.original;
      }
      // the reference doesn't exist, so revert to plain text
      else {
        return attrs.original;
      }
      break;
  }

  // convert all the children
  i = 1;

  // deal with the attribute node, if it exists
  if ( attrs ) {
    // if there are keys, skip over it
    for ( var key in jsonml[ 1 ] ) {
        i = 2;
        break;
    }
    // if there aren't, remove it
    if ( i === 1 ) {
      jsonml.splice( i, 1 );
    }
  }

  for ( ; i < jsonml.length; ++i ) {
    jsonml[ i ] = convert_tree_to_html( jsonml[ i ], references, options );
  }

  return jsonml;
}


// merges adjacent text nodes into a single node
function merge_text_nodes( jsonml ) {
  // skip the tag name and attribute hash
  var i = extract_attr( jsonml ) ? 2 : 1;

  while ( i < jsonml.length ) {
    // if it's a string check the next item too
    if ( typeof jsonml[ i ] === "string" ) {
      if ( i + 1 < jsonml.length && typeof jsonml[ i + 1 ] === "string" ) {
        // merge the second string into the first and remove it
        jsonml[ i ] += jsonml.splice( i + 1, 1 )[ 0 ];
      }
      else {
        ++i;
      }
    }
    // if it's not a string recurse
    else {
      merge_text_nodes( jsonml[ i ] );
      ++i;
    }
  }
}

} )( (function() {
  if ( typeof exports === "undefined" ) {
    window.markdown = {};
    return window.markdown;
  }
  else {
    return exports;
  }
} )() );

define("markdown", (function (global) {
    return function () {
        var ret, fn;
        return ret || global.markdown;
    };
}(this)));

define('window-manager/windows/MarkdownWindow',[
	'markdown',
	'./Window'
], function (
	Markdown,
	Window
	) {


	function scrollToElementFactory(element) {
		return function (e) {
			element.scrollIntoView();
			e.preventDefault();
			e.stopPropagation();
		}
	}
	function MarkdownWindow (id, name, md) {
		Window.call(this, id, name);

		this.markdown = md;
		this.documentElement = null;

		this.addFlag('markdown');
	}

	MarkdownWindow.prototype = Object.create(Window.prototype);
	MarkdownWindow.prototype.constructor = MarkdownWindow;

	MarkdownWindow.prototype.createContentElement = function() {
		var contentElement = document.createElement('div');

		var tocElement = document.createElement('nav');
		tocElement.classList.add('window__sidebar');

		var documentElement = document.createElement('div');
		documentElement.classList.add('window__document');
		documentElement.innerHTML = Markdown.toHTML(this.markdown);

		var headerElementNames = ['h1', 'h2', 'h3', 'h4', 'h5', 'h6'];
		var nodeIterator = document.createNodeIterator(
			documentElement,
			NodeFilter.SHOW_ELEMENT,
			function(node) {
				return headerElementNames.indexOf(node.nodeName.toLowerCase()) >= 0;
			},
			true // deprecated argument, but IE
		);
		var node;

		var i = 0;
		while ((node = nodeIterator.nextNode())) {
			++i;

			var level = parseInt(node.nodeName.substr(1)),
				id = (this.id + '-'+ i).toLowerCase(),
				hyperlinkElement = document.createElement('a'),
				originalElement = node;

			originalElement.setAttribute('id', id);
			hyperlinkElement.addEventListener('click', scrollToElementFactory(originalElement));

			originalElement.setAttribute('header-id', i);
			originalElement.setAttribute('header-level', level);

			hyperlinkElement.setAttribute('header-id', i);
			hyperlinkElement.setAttribute('header-level', level);
			hyperlinkElement.classList.add('window__item');

			hyperlinkElement.appendChild(document.createTextNode(originalElement.innerText || originalElement.innerHTML));
			tocElement.appendChild(hyperlinkElement);
		}

		contentElement.appendChild(tocElement);
		contentElement.appendChild(documentElement);

		this.documentElement = documentElement;

		return contentElement;
	};

	return MarkdownWindow;
});
define('panvas/main',[
	'tiny-emitter'
], function(TinyEmitter) {
	'use strict';

	/**
	 * - Likens to a frame, that you can put a (cutout) of a picture in. The picture in this case is the bare minimum of
	 *   what we need to know about "content"
	 * - Panvas therefore has it's own dimensions versus the contents
	 * - must be able to zoom, pan and scroll
	 *
	 * @note: uses "z" for *zoom* and "w", "h", "x", "y" respectively for width, height, left and top.
	 *        because its shorter.
	 * @constructor
	 */

	var panControls = {
		'up': {
			label: '&#8598;',
			tooltip: 'Pan upwards',
			onClick: function(canvas) {
				canvas.panFrame(50 / canvas.frame.zoom, 0, true);
				canvas.commit();
			}
		},
		'right': {
			label: '&#8599;',
			tooltip: 'Pan to the right',
			onClick: function(canvas) {
				canvas.panFrame(0, -50 / canvas.frame.zoom, true);
				canvas.commit();
			}
		},
		'down': {
			label: '&#8600;',
			tooltip: 'Pan downwards',
			onClick: function(canvas) {
				canvas.panFrame(-50 / canvas.frame.zoom, 0, true);
				canvas.commit();
			}
		},
		'left': {
			label: '&#8601;',
			tooltip: 'Pan to the left',
			onClick: function(canvas) {
				canvas.panFrame(0, 50 / canvas.frame.zoom, true);
				canvas.commit();
			}
		}
	};
	var zoomControls = {
		'zoom-in': {
			label: '+',
			tooltip: 'Zoom in by 50%',
			onClick: function(canvas) {
				canvas.setZoom(1.5, true);
				canvas.commit();
			}
		},
		'1-1': {
			label: '1:1',
			tooltip: 'Zoom to actual pixels',
			onClick: function(canvas) {
				canvas.setZoom(1, false);
				//canvas.panFrame(0,0);
				canvas.commit();
			}
		},
		'reset': {
			label: 'R',
			tooltip: 'Reset zoom to fit window',
			onClick: function(canvas) {
				canvas.resetPositioning();
			}
		},
		'zoom-out': {
			label: '-',
			tooltip: 'Zoom out by 50%',
			onClick: function(canvas) {
				canvas.setZoom(1/1.5, true);
				canvas.commit();
			}
		}
	};
	function Panvas (frame, pictureUrl) {
		TinyEmitter.call(this);

		this.container = frame;
		this.container.classList.add('panvas');
		this.container.classList.add('panvas__frame');

		var controlsElement = document.createElement('div');
		controlsElement.classList.add('panvas__controls');
		this.container.appendChild(controlsElement);


		var zoomControlsElement = document.createElement('div');
		zoomControlsElement.classList.add('panvas__controls__zoom');
		controlsElement.appendChild(zoomControlsElement);
		Object.keys(zoomControls).forEach(function (direction) {
			var el = document.createElement('div');
			el.classList.add('panvas__controls__zoom--' + direction);
			el.setAttribute('title', zoomControls[direction].tooltip);
			el.innerHTML = zoomControls[direction].label;
			el.addEventListener('click', zoomControls[direction].onClick.bind(undefined, this));
			zoomControlsElement.appendChild(el);
		}.bind(this));

		var panControlsElement = document.createElement('div');
		panControlsElement.classList.add('panvas__controls__pan');
		controlsElement.appendChild(panControlsElement);
		Object.keys(panControls).forEach(function (direction) {
			var el = document.createElement('div');
			el.classList.add('panvas__controls__pan--' + direction);
			el.setAttribute('title', panControls[direction].tooltip);
			el.innerHTML = panControls[direction].label;
			el.addEventListener('click', panControls[direction].onClick.bind(undefined, this));
			panControlsElement.appendChild(el);
		}.bind(this));

		if(pictureUrl)
			this.load(pictureUrl);
	}

	Panvas.prototype = Object.create(TinyEmitter.prototype);
	Panvas.prototype.constructor = Panvas;

	Panvas.prototype.load = function(pictureUrl) {
		var content = new Image();
		content.src = pictureUrl;

		this.container.classList.add('panvas--loading');

		content.onload = function() {


			if(this.content)
				this.container.removeChild(this.content);

			this.content = content;
			this.content.classList.add('panvas__picture');
			this.content.setAttribute('draggable', 'false');
			this.container.appendChild(this.content);
			this.container.classList.remove('panvas--loading');

			this.picture = this.getDimensions(this.content);
			this.frame = this.getDimensions(this.container);

			this.commitFrame();
			this.resetPositioning();

			this.emit('loaded');
		}.bind(this);

		content.onerror = function (){
			this.container.classList.remove('panvas--loading');
			this.container.classList.add('panvas--error');

			this.emit('error');
		}.bind(this);
	};

	Panvas.prototype.resizeFrame = function (width, height) {
		this.frame.w = width;
		this.frame.h = height;
		this.frame.r = width / height;
	};

	Panvas.prototype.panFrame = function (down, right, additive) {
		this.frame.x = (additive ? this.frame.x : 0) + right;
		this.frame.y = (additive ? this.frame.y : 0) + down;
	};

	Panvas.prototype.commit = function() {
		var picturePixel = {
				w: (this.frame.zoom * this.picture.w),
				h: (this.frame.zoom * this.picture.h)
			},
			normalizedOffset = this.getNormalizedOffset(
				picturePixel,
				this.frame
			);

		this.content.style.width  = picturePixel.w + 'px';
		this.content.style.height = picturePixel.h + 'px';
		this.content.style.top    = normalizedOffset.y + (this.frame.zoom * this.frame.y) + 'px';
		this.content.style.left   = normalizedOffset.x + (this.frame.zoom * this.frame.x) + 'px';
	};

	Panvas.prototype.commitFrame = function() {
		this.container.style.width = (this.frame.w) + 'px';
		this.container.style.height = (this.frame.h) + 'px';
	};

	Panvas.prototype.setZoom = function(ratio, multiply) {
		this.frame.zoom = multiply ? ratio * this.frame.zoom : ratio;
	};

	Panvas.prototype.setZoomForContain = function(picture) {
		picture = picture || this.picture;

		this.setZoom(this.contentIsWider()
			? this.frame.w / picture.w
			: this.frame.h / picture.h)
	};

	Panvas.prototype.contentIsWider = function(frame, picture) {
		frame = frame || this.frame;
		picture = picture || this.picture;

		return picture.r > frame.r;
	};


	Panvas.prototype.getDimensions = function(element) {
		element = element instanceof Image
			? element
			: element.getBoundingClientRect();
		return {
			w: element.width,
			h: element.height,
			r: element.width / element.height
		};
	};

	/**
	 * Get the offset in actual pixels that it would take to place picture center in frame center
	 */
	Panvas.prototype.getNormalizedOffset = function(picture, frame) {
		return {
			x: (frame.w - picture.w) / 2,
			y: (frame.h - picture.h) / 2
		};
	};
	Panvas.prototype.resetPositioning = function() {
		this.panFrame(0, 0);
		this.setZoomForContain();

		this.commit();
	};
	Panvas.prototype.zoom = function () {
		this.setZoom.apply(this, arguments);
		this.commit();
	};
	Panvas.prototype.pan = function () {
		this.panFrame.apply(this, arguments);
		this.commit();
	};

	return Panvas;



});
define('panvas', ['panvas/main'], function (main) { return main; });

define('window-manager/windows/ImageWindow',[
	'panvas',
	'./Window'
], function (
	Panvas,
	Window
	) {


	function PortfolioImage (url) {
		this.url = url;
		this.thumbnail = this.createThumbnailElement();
	}
	PortfolioImage.prototype.getFullUrl = function() {
		return require.toUrl('portfolio/' + this.url)
	};
	PortfolioImage.prototype.getThumbnailUrl = function() {
		return require.toUrl('portfolio/generated/thumb/' + this.url)
	};
	PortfolioImage.prototype.createThumbnailElement = function() {
		var imageLinkElement = document.createElement('a'),
			imageElement = new Image();

		// edit thumbnail URL here
		imageElement.src = this.getThumbnailUrl();

		imageLinkElement.appendChild(imageElement);

		return imageLinkElement;
	};

	/**
	 * @TODO: Thumbnail URLs
	 * @param id
	 * @param name
	 * @param allImages
	 * @param currentImage
	 * @constructor
	 */

	function ImageWindow (id, name, allImages, currentImage) {
		Window.call(this, id, name);

		this.allImages = (Array.isArray(allImages) ? allImages : [allImages]).map(function(img) {
			return new PortfolioImage(img)
		}.bind(this));
		this.currentImage = currentImage || 0;

		this.addFlag('image');
	}

	ImageWindow.prototype = Object.create(Window.prototype);
	ImageWindow.prototype.constructor = ImageWindow;

	ImageWindow.prototype.createThumbnailsElement = function() {
		var thumbnailsElement = document.createElement('div');

		this.allImages.forEach(function(image) {
			image.thumbnail.addEventListener('click', function(e) {
				this.openImage(image);
				e.preventDefault();
				e.stopPropagation();
			}.bind(this));

			image.thumbnail.classList.add('window__thumbnail');
			thumbnailsElement.appendChild(image.thumbnail);

		}.bind(this));

		return thumbnailsElement;
	};

	ImageWindow.prototype.getCurrentImage = function() {
		return this.allImages[this.currentImage];
	};

	ImageWindow.prototype.openImage = function(image) {
		if(image)
			this.currentImage = image instanceof PortfolioImage ? this.allImages.indexOf(image) : image;

		this.canvas.load(this.getCurrentImage().getFullUrl());
	};

	ImageWindow.prototype.createContentElement = function() {

		var contentElement = document.createElement('div');

		if(this.allImages.length > 1) {
			var thumbnailsElement = this.createThumbnailsElement();
			thumbnailsElement.classList.add('window__sidebar');
			thumbnailsElement.classList.add('window__thumbnails');
			contentElement.appendChild(thumbnailsElement);
		}

		var documentElement = document.createElement('article');
		documentElement.classList.add('window__document');

		var canvasElement = document.createElement('div');
		canvasElement.classList.add('window__canvas');

		this.documentElement = documentElement;

		var canvas = new Panvas(canvasElement);
		this.canvas = canvas;

		documentElement.appendChild(canvasElement);

		this.on('resized', function () {
			var bb = this.documentElement.getBoundingClientRect();
			canvas.resizeFrame(bb.width - 7, bb.height - 7);
			canvas.commitFrame();
			canvas.commit();
		}.bind(this));
		this.openImage();

		contentElement.appendChild(documentElement);

		return contentElement;
	};

	return ImageWindow;
});
define('window-manager/main',[
	'./DraggableElement',
	'./WindowManager',

	'./windows/BasicWindow',
	'./windows/MarkdownWindow',
	'./windows/ImageWindow'
], function (
	DraggableElement,
	WindowManager,
	BasicWindow,
	MarkdownWindow,
	ImageWindow
) {
	return {
		DraggableElement: DraggableElement,
		WindowManager: WindowManager,

		BasicWindow: BasicWindow,
		MarkdownWindow: MarkdownWindow,
		ImageWindow: ImageWindow
	};
});
define('window-manager', ['window-manager/main'], function (main) { return main; });

define('core/commands/debug',[], function() {

	return function(app) {

		var debugCommand = app.command.addCommand('debug', function(req, res) {
			if(app.hasFlag('debug-mode')) {
				res.log('Debug mode is currently: engaged');
				req.command.getCommandByName('off').execute(req, res);
			} else {
				res.log('Debug mode is currently: disengaged');
				req.command.getCommandByName('on').execute(req, res);
			}
		})
			.addDescription('Toggle debug mode');

		debugCommand.addCommand('on', function(req, res) {
				app.addFlag('debug-mode');
				app.output.scrollToBottom(); // avoid waiting 50ms for output-and-scroll

				res.log('Engaging debug mode...');
				res.log('Debug and error objects are now expanded. Type <a command="debug off">debug off</a> to disable it again.');
			})
			.addDescription('Engage debug mode');

		debugCommand.addCommand('off', function(req, res) {
				app.removeFlag('debug-mode');
				res.log('Disengaging debug mode...');
				res.log('Debug and error objects are now collapsed. Type <a command="debug on">debug on</a> to enable it again.');
			})
			.addDescription('Disengage debug mode');

		debugCommand.addCommand('prune', function(req, res) {
				req.app.output.pruneRenderedOutput(req.options.length || 5);
			})
			.addDescription('Trim output log to given length, defaults to 5')
			.addOption('length', 'l', 'Number of log items to retain', false, 'n');

	};

});
define('core/commands/help',[], function () {
	var SEP = '\t',
		SEPP = SEP + SEP;

	return function(app) {
		app.command.addCommand('help', function(req, res) {
			var commandManager = req.app.command,
				root = commandManager.getCommandForRoute(req.route.slice(1), true);
			res.header('Help');
			res.log('HELP FILE FOR ' + root.getRoute().join('/').toUpperCase()+'');

			if(root.description)
				res.log(root.description);

			if(root.listCommands().length) {
				res.log();
				res.log('Child commands');
				root.listCommands().sort(function(a, b) {
					return a.name < b.name ? -1 : 1;
				}).forEach(function (command) {
					res.log(SEP + '<a command="help '+command.getRoute().slice(1).join(' ')+'">?</a>' + ' ' + '<a command="'+command.getRoute().slice(1).join(' ')+'">'+command.name+'</a>' + SEPP + command.description);
				});
			}

			if(root.listOptions().length) {
				res.log();
				res.log('Options');
				root.listOptions().sort(function(a, b) {
					return a.long < b.long ? -1 : 1;
				}).forEach(function (option) {
					res.log(SEP + [
						option.short ? '-' + option.short : null,
							'--' + option.long + (option.type ? ' &#60;' + option.type + '&#62;' : ''),
						option.description].join(SEP));
				});
			}
		})
			.addDescription('Prints the help files, sort of')
			.isGreedy();

	};



});
define('core/Application',[
	'base64',

	'input-manager',
	'output-manager',
	'command-manager',
	'window-manager',

	'./commands/debug',
	'./commands/help'

], function (
	base64,
	$input,
	$output,
	$command,
	$window,

	debugCommandFactory,
	helpCommandFactory

) {


	function Application(element) {
		this.flags = [];
		this.element = element || document.body;
		this.input = new $input.InputManager();
		this.output = new $output.OutputManager();
		this.command = new $command.CommandManager(document.title);
		this.window = new $window.WindowManager();

		this.input.captureMagicHref(this.element);

		// update suggestions when user types
		this.input.onChange(function(value) {
			var suggestedCommands = this.command.getSuggestedCommandsForInput(value);
			this.input.suggestions.populateFromCommands(suggestedCommands.sort(function(a, b) {
				return a.name < b.name ? -1 : 1;
			}));
		}.bind(this));

		setTimeout(function() {
			// hack, at this time there have been no registered commands
			this.input.suggestions.populateFromCommands(this.command.listCommands().sort(function(a, b) {
				return a.name < b.name ? -1 : 1;
			}));
		}.bind(this));

		// write to log when user submits
		this.input.onSubmit(function(value) {
			this.output.input(value);
		}.bind(this));

		// update page title
		var originalDocumentTitle = document.title,
			pageTitleElement = document.getElementById('pagetitle');

		if(pageTitleElement)
			this.input.onSubmit(function(value) {
				document.title = originalDocumentTitle + ' - '+value.input;
				pageTitleElement.innerHTML = document.title;
			}.bind(this));

		// find and execute controller when user submits
		this.input.onSubmit(function(value) {
			// Construct req/res, start controllers etc.
			var req = value,
				res = this.output;
			req.app = this;

			try {
				this.command.executeCommandForRequest(req, res);
			} catch (error) {
				res.error(error);
			}
		}.bind(this));

		// keep the latest input in URL bar, and vice versa
		this.input.onSubmit(function(value) {
			window.history.pushState({input: value.input}, value.input, '#!/' + (value.input.indexOf(' ') >= 0 ? '~' + base64.encode(value.input) : value.input));
		});

		this.input.onMagicHref(function(value) {
			this.input.submit(value);
		}.bind(this));

		// load core-specific commands
		[
			debugCommandFactory,
			helpCommandFactory
		].forEach(function(commandFactory) {
			commandFactory(this);
		}.bind(this));

		this.input.focusField(true);

	}

	Application.prototype.addFlag = function(flag) {
		if(!this.flags)
			this.flags = [];

		this.flags.push(flag);

		if(this.element)
			this.element.classList.add(flag);
	};

	Application.prototype.hasFlag = function(flag) {
		return this.flags.indexOf(flag) >= 0;
	};

	Application.prototype.removeFlag = function(flag) {
		if(this.flags)
			this.flags.splice(this.flags.indexOf(flag), 1);

		if(this.element)
			this.element.classList.remove(flag);
	};



	return Application;
});
define('core/main',[
	'./Application'
], function (
	Application
) {
	return {
		Application: Application
	}
});
define('core', ['core/main'], function (main) { return main; });

define('sensor-manager/sensors/Sensor',[], function() {

	function Sensor (id) {
		this.id = id;
	}

	// MUST IMPLEMENT:

	Sensor.prototype.start = function () {
		throw new Error('Not implemented');
	};

	Sensor.prototype.stop = function () {
		throw new Error('Not implemented');
	};
	Sensor.prototype.isActive = function() {
		throw new Error('Not implemented');
	};
	Sensor.prototype.reset = function () {
		throw new Error('Not implemented');
	};

	Sensor.prototype.getElement = function () {
		throw new Error('Not implemented');
	};

	Sensor.prototype.registerValue = function(y, x) {
		throw new Error('Not implemented');
	};

	// end of must implement

	Sensor.prototype.destroy = function () {
		this.stop();
		this.getElement().parentNode.removeChild(this.getElement());
	};

	Sensor.prototype.getSummary = function(obj) {
		if(typeof obj !== 'object')
			obj = {};

		obj.id = this.id;

		return obj;
	};

	return Sensor;

});
define('canvases/Canvas',[], function() {

	var setAnimationFrameForFps = (function(){
		return window.requestAnimationFrame       ||
			window.webkitRequestAnimationFrame ||
			window.mozRequestAnimationFrame    ||
			function(callback , timeout){
				window.setTimeout(callback, timeout || 1000);
			};
	})();

	function Canvas(width, height, fps) {
		this.active = false;

		this.fps = fps;
		this.frame = 0;

		this._createElement(width || 320, height || 240);

		this.onInit();
	}

	// Private functions, do not use
	Canvas.prototype._createElement = function(width, height) {
		var element = document.createElement('canvas');
		element.classList.add('canvas');

		this.element = element;

		this.resize(width, height);

		return element;
	};
	Canvas.prototype._loop = function() {
		if(!this.active)
			return;

		var now = new Date().getTime(),
			last = this.lastFrame;

		if(this.fps && (now-last) < (1000/this.fps)) {
			setAnimationFrameForFps(this._loop.bind(this), this.fps);
			return;
		}

		this.loopOne(now);

		if(this.fps <= 5) // from 5 fps or below, use setTimeout rather than setAnimationFrame
			setTimeout(this._loop.bind(this), 1000/this.fps);
		else
			setAnimationFrameForFps(this._loop.bind(this), 1000/this.fps);
	};

	/////
	// API, YOU MAY CALL
	/////
	Canvas.prototype.getWidth = function() {
		return parseInt(this.element.width);
	};
	Canvas.prototype.getHeight = function() {
		return parseInt(this.element.height);
	};
	Canvas.prototype.resize = function(width, height) {
		if(width) {
			this.element.setAttribute('width', width);
		}
		if(height) {
			this.element.setAttribute('height', height);
		}
		this.context = this.element.getContext("2d");

		this.onResize();
	};
	Canvas.prototype.start = function() {
		if(this.active)
			return;

		this.active = true;

		this.onStart();

		this._loop();
	};
	Canvas.prototype.loopOne = function(now) {
		this.iterate();

		this.clear();

		this.draw();

		++this.frame;

		this.lastFrame = now || new Date().getTime();
	};
	Canvas.prototype.iterate = function() {
		this.onIterate.apply(this, arguments);
	};
	Canvas.prototype.draw = function() {
		this.onDraw.apply(this, arguments);
	};
	Canvas.prototype.clear = function() {
		this.onClear.apply(this, arguments);
	};
	Canvas.prototype.stop = function() {
		if(!this.active)
			return;

		this.active = false;

		this.onStop();
	};


	/////
	// CUSTOMIZATION HOOKS, TO BE OVERWRITTEN
	/////
	Canvas.prototype.onInit = function() {

	};
	Canvas.prototype.onResize = function() {

	};
	Canvas.prototype.onStart = function() {

	};
	Canvas.prototype.onIterate = function() {
		throw new Error('Not implemented');
	};
	Canvas.prototype.onClear = function() {
		this.context.clearRect(0, 0, this.element.width, this.element.height);
	};
	Canvas.prototype.onDraw = function() {
		throw new Error('Not implemented');
	};
	Canvas.prototype.onStop = function() {

	};

	return Canvas;
});

define('canvases/Banshee',[
	'./Canvas'
], function(Canvas) {


	var BANSHEE_DEFAULTS= {
		color: '#414141',
		background: false,
		datapointWidth: 1,
		datapointSpacing: 3,
		datapointsPerSecond: 20,
		excitementDecay: 0.5,

		inaccuracy: 0.1, // 0.1
		deviation: 1 // 1
	};

	function Banshee(width, height, options) {
		this.options = {};
		Object.keys(BANSHEE_DEFAULTS).forEach(function(key) {
			if(!BANSHEE_DEFAULTS.hasOwnProperty(key))
				return;
			this.options[key] = (!options || options[key] === undefined) ? BANSHEE_DEFAULTS[key] : options[key];
		}.bind(this));

		this.datapoints = [];

		this.excitement = 0;

		this.datapointTimer = null;

		Canvas.call(this, width || 128, height || 64, 25);

		this.element.classList.add('banshee');
	}

	Banshee.prototype = Object.create(Canvas.prototype);
	Banshee.prototype.constructor = Banshee;

	Banshee.prototype.onInit = function() {
		if(!this.element)
			throw new Error('Cannot initialize Canvas without element');
		if(!this.options)
			this.options = {};


		var context = this.context;
		context.strokeStyle = this.options.color;
		context.fillStyle = this.options.color;
		context.lineWidth = 1;
	};
	Banshee.prototype.onResize = function() {
		this.info = {
			visibleDatapoints: (this.getWidth() - this.options.datapointSpacing) / (this.options.datapointWidth + this.options.datapointSpacing)
		};
	};
	Banshee.prototype.onStart = function() {
		this.datapointTimer = setInterval(function() {
			this.addDatapoint();
		}.bind(this), 1000/(this.options.datapointsPerSecond||25));
	};
	Banshee.prototype.onIterate = function() {
		if(this.excitement > 0.01)
			this.excitement = this.excitement * this.options.excitementDecay;

	};

	// onClear is inherited

	Banshee.prototype.onDraw = function() {
		var context = this.context;
		maxHeight = 1;

		this.datapoints.forEach(function(datapoint, i) {
			var height = datapoint.value;

			var urgency = height / maxHeight,
				color = [];
			if(urgency > 1.3)
				color = [200,0,0,1];
			else if(urgency > 1)
				color = [170,170,170,1];
			else if(urgency > 0.025)
				color = [100,100,100,1];
			else
				color = [50,50,50,1];


			context.fillStyle = 'rgba(' + color.join(', ') + ')';

			height = height * this.getHeight() / 2 + 1;

			context.fillRect(
					this.options.datapointSpacing + i * (this.options.datapointWidth+this.options.datapointSpacing),
					this.getHeight()/2 - 0.5 - height + datapoint.skew * 0.3 * height,
				this.options.datapointWidth,
					2 * height
			);
		}.bind(this));

		//drawSine.apply(this, [this.frame, this.height/2, 0]);
		this.context.stroke();
	};

	Banshee.prototype.onStop = function() {
		clearInterval(this.datapointTimer);
	};


	Banshee.prototype.addDatapoint = function (excitement) {
		this.excitement = this.excitement + (excitement || 0);

		var datapoint = {
			//value: (Math.random() * 2 -1) * (this.excitement + Math.random() * 0.01),
			value: this.excitement + (Math.random()-0.5) * this.options.inaccuracy,
			//value: Math.abs(Math.sin(this.frame * 0.1)),
			skew: (Math.random()*2 - 1) * this.options.deviation
		};

		this.datapoints.unshift(datapoint);

		if(this.datapoints.length > this.info.visibleDatapoints)
			this.datapoints.pop();
	};


	return Banshee;
});

define('canvases/main',[
//	'./Canvas',
	'./Banshee'
], function(
//	Canvas,
	Banshee
	) {

	return {
//		Canvas: Canvas,

		Banshee: Banshee
	}
});

define('canvases', ['canvases/main'], function (main) { return main; });

define('sensor-manager/sensors/BansheeSensor',[
	'canvases',
	'./Sensor'
], function(canvases, Sensor) {


	function BansheeSensor(id, options) {
		Sensor.call(this, id);

		if(!options)
			options = {};

		this.banshee = new canvases.Banshee(250, 25, options);

		this.element = document.createElement('div');
		this.element.classList.add('sensor');

		var labelElement = document.createElement('div');
		labelElement.classList.add('sensor__label');
		labelElement.appendChild(document.createTextNode(this.id));

		var canvasWrapperElement = document.createElement('div');
		canvasWrapperElement.classList.add('sensor__canvas');
		canvasWrapperElement.appendChild(this.banshee.element);
		this.canvasWrapper = canvasWrapperElement;

		this.element.appendChild(labelElement);
		this.element.appendChild(canvasWrapperElement);

	}

	BansheeSensor.prototype = Object.create(Sensor.prototype);
	BansheeSensor.prototype.constructor = BansheeSensor;

	// y = vertical axis, the value you want to record
	// x = horizontal axis, not required since it could be equivelant to passage of (real)time
	BansheeSensor.prototype.registerValue = function(y, x) {
		this.banshee.excitement = this.banshee.excitement + y;
	};

	BansheeSensor.prototype.isActive = function() {
		return !!this.banshee.active;
	};

	BansheeSensor.prototype.start = function() {
		this.banshee.excitement = 0;
		this.banshee.start();

		var bb = this.banshee.element.parentNode.getBoundingClientRect();

		this.setStatus(true);

		this.banshee.resize(bb.width);
	};
	BansheeSensor.prototype.stop = function(status) {
		this.setStatus(status || 'Stopped');
		this.banshee.stop();
	};

	BansheeSensor.prototype.getElement = function() {
		return this.element;
	};

	BansheeSensor.prototype.delayedStart = function (status, time) {
		this.setStatus(status || 'Starting');
		setTimeout(function () {
			this.start();
		}.bind(this), time || (1000 + Math.round(Math.random() * 1000)));
	};

	BansheeSensor.prototype.setStatus = function (status) {
		if(status === true) {
			this.element.classList.add('sensor--started');
			this.element.classList.remove('sensor--stopped');
			this.canvasWrapper.setAttribute('status-text', 'Running');
			return;
		}

		this.element.classList.remove('sensor--started');
		this.element.classList.add('sensor--stopped');
		this.canvasWrapper.setAttribute('status-text', status || '');
	};

	BansheeSensor.prototype.getSummary = function() {
		var summary = Sensor.prototype.getSummary.apply(this, arguments);
		//summary.bansheeOptions = this.banshee.options;
		summary.bansheeOInfo = this.banshee.info;
		summary.bansheeRuntime = {
			datapoints: this.banshee.datapoints.length
		};
		return summary;
	}

	return BansheeSensor;

});
define('sensor-manager/SensorManager',[
	'object-store',

	'./sensors/Sensor',
	'./sensors/BansheeSensor'
], function (
	ObjectStore,
	Sensor,
	BansheeSensor
) {
	function SensorManager(element) {
		if(!element) {
			this.disabled = true;
		}

		ObjectStore.call(this, {
			requireInstanceOf: Sensor
		});

		this.element = element;
	}

	SensorManager.prototype = Object.create(ObjectStore.prototype);
	SensorManager.prototype.constructor = SensorManager;

	SensorManager.prototype.addSensor = function (id, options, doNotStart) {
		if(this.disabled)
			return;

		var sensor = this.set(id instanceof Sensor ? id : new BansheeSensor(id, options));
		this.element.appendChild(sensor.getElement());

		if(!doNotStart) {
			sensor.delayedStart('Starting');
		} else {
			sensor.stop('Idle');
		}

		return sensor;
	};

	SensorManager.prototype.removeSensor = function(id) {
		if(this.disabled)
			return;

		var sensor = this.get(id);

		sensor.destroy();

		this.delete(id);
	};

	SensorManager.prototype.registerValue = function(id, y, x) {
		if(this.disabled)
			return;

		var sensor = this.get(id);

		sensor.registerValue(y, x);
	};

	return SensorManager;
});
/**
 * A JavaScript project for accessing the accelerometer and gyro from various devices
 *
 * @author Tom Gallacher <tom.gallacher23@gmail.com>
 * @copyright Tom Gallacher <http://www.tomg.co>
 * @version 0.0.1a
 * @license MIT License
 * @options frequency, callback
 */
(function (root, factory) {
		if (typeof define === 'function' && define.amd) {
				// AMD. Register as an anonymous module.
				define('gyro',factory);
		} else if (typeof exports === 'object') {
				// Node. Does not work with strict CommonJS, but
				// only CommonJS-like enviroments that support module.exports,
				// like Node.
				module.exports = factory();
		} else {
				// Browser globals (root is window)
				root.returnExports = factory();
	}
}(this, function () {
	var measurements = {
				x: null,
				y: null,
				z: null,
				alpha: null,
				beta: null,
				gamma: null
			},
			calibration = {
				x: 0,
				y: 0,
				z: 0,
				alpha: 0,
				beta: 0,
				gamma: 0
			},
			interval = null,
			features = [];

	var gyro = {};

	/**
	 * @public
	 */
	gyro.frequency = 500; //ms

	gyro.calibrate = function() {
		for (var i in measurements) {
			calibration[i] = (typeof measurements[i] === 'number') ? measurements[i] : 0;
		}
	};

	gyro.getOrientation = function() {
		return measurements;
	};

	gyro.startTracking = function(callback) {
		interval = setInterval(function() {
			callback(measurements);
		}, gyro.frequency);
	};

	gyro.stopTracking = function() {
		clearInterval(interval);
	};

	/**
	 * Current available features are:
	 * MozOrientation
	 * devicemotion
	 * deviceorientation
	 */
	gyro.hasFeature = function(feature) {
		for (var i in features) {
			if (feature == features[i]) {
				return true;
			}
		}
		return false;
	};

	gyro.getFeatures = function() {
		return features;
	};


	/**
	 * @private
	 */
	// it doesn't make sense to depend on a "window" module
	// since deviceorientation & devicemotion make just sense in the browser
	// so old school test used.
	if (window && window.addEventListener) {
		function setupListeners() {
			window.addEventListener('MozOrientation', function(e) {
				features.push('MozOrientation');
				measurements.x = e.x - calibration.x;
				measurements.y = e.y - calibration.y;
				measurements.z = e.z - calibration.z;
			}, true);

			window.addEventListener('devicemotion', function(e) {
				features.push('devicemotion');
				measurements.x = e.accelerationIncludingGravity.x - calibration.x;
				measurements.y = e.accelerationIncludingGravity.y - calibration.y;
				measurements.z = e.accelerationIncludingGravity.z - calibration.z;
			}, true);

			window.addEventListener('deviceorientation', function(e) {
				features.push('deviceorientation');
				measurements.alpha = e.alpha - calibration.alpha;
				measurements.beta = e.beta - calibration.beta;
				measurements.gamma = e.gamma - calibration.gamma;
			}, true);
		}
		setupListeners();
	}

	return gyro;
}));

define('sensor-manager/sensors/GyroBansheeSensor',[
	'gyro',
	'./BansheeSensor'
], function(gyro, BansheeSensor) {

	function GyroBansheeSensor(id, options) {
		BansheeSensor.call(this, id);

	}

	GyroBansheeSensor.prototype = Object.create(BansheeSensor.prototype);
	GyroBansheeSensor.prototype.constructor = GyroBansheeSensor;

	GyroBansheeSensor.prototype.start = function(req, res) {
		BansheeSensor.prototype.start.apply(this, arguments);

		if(res) {
			res.log('Initializing gyro tracker, detecting features...');

			var features = gyro.getFeatures();
			res.log('... detected ' + features.length + ' gyro features: ' + features.join(', '));

			if (!features.length)
				return res.log('Initializing gyro aborted, no detected features');

			res.log('Gyro engaged, polling rate ' + (1000 / this.getFrequency()) + '/second');
		}

		gyro.startTracking(function(gyroData) {
			this.registerValue(0.3);
			//res.log(JSON.stringify(gyroData));
		}.bind(this));
	};
	GyroBansheeSensor.prototype.stop = function() {
		BansheeSensor.prototype.stop.apply(this, arguments);
		gyro.stopTracking();
	};
	GyroBansheeSensor.prototype.getFeatures = function() {
		return gyro.getFeatures.apply(gyro, arguments);
	};
	GyroBansheeSensor.prototype.getFrequency = function() {
		return gyro.frequency;
	};

	return GyroBansheeSensor;

});
define('sensor-manager/main',[
	'./SensorManager',

	'./sensors/Sensor',
	'./sensors/BansheeSensor',
	'./sensors/GyroBansheeSensor'
], function (
	SensorManager,

	Sensor,
	BansheeSensor,
	GyroBansheeSensor,

	commandsFactory
) {

	return {
		SensorManager: SensorManager,

		Sensor: Sensor,
		BansheeSensor: BansheeSensor,
		GyroBansheeSensor: GyroBansheeSensor
	};
});
define('sensor-manager', ['sensor-manager/main'], function (main) { return main; });

define('sensor-manager/module',[
	'./main'
], function ($sensor) {

	return function(app) {


		app.sensor = new $sensor.SensorManager(document.getElementById('sensors'));
		app.sensor.addSensor('keyboard');
		app.sensor.addSensor('operations');
		app.sensor.addSensor('dom lvl', {
			excitementDecay: 1,
			deviation: 2,
			inaccuracy: 0.5
		});
		app.sensor.addSensor('i/o');



		if(!app.sensor.disabled)
			setInterval(function () {
				var elements = document.querySelectorAll(':hover'),
					sensor = app.sensor.get('dom lvl');
				sensor.banshee.excitement = elements ? (elements.length - 3) / 6 : 0;
			}, 250);

		app.sensor.addSensor(new $sensor.GyroBansheeSensor('gyro', {
			datapointsPerSecond: 40,
			excitementDecay: 0.7
		}), null, true);

		// register value congruent to actual HTML length for a logged message
		app.output.onRender(function(output, target) {
			var wrap = document.createElement('div');
			wrap.appendChild(target.cloneNode(true));
			app.sensor.registerValue('i/o', wrap.innerHTML.length/750);
		});

		// excite the banshee when user types
		app.input.onChange(function() {
			app.sensor.registerValue('keyboard', 0.3);
		});

		// excite the banshee when user submits
		app.input.onSubmit(function() {
			app.sensor.registerValue('operations', 1);
		}.bind(this));


		function getSensorsForQuery(req, res) {
			var selectedSensors = [];
			if(req.options.all) {
				selectedSensors = app.sensor.list();
			} else if(req.options.sensor) {
				selectedSensors.push(app.sensor.get(req.options.sensor));
			}

			if(!selectedSensors.length) {
				res.log('No sensors selected! See also <a command="sensors list">sensors list</a> and <a command="help sensors toggle">help sensors toggle</a>');
				return [];
			}
1
			return selectedSensors;
		}

		function describeArgumentsForQuery(command) {
			command
				.addOption('all', 'a', 'Select all sensors')
				.addOption('sensor', 's', 'Select sensor by ID');
		}
		var sensorCommand = app.command.addCommand('sensors')
			.addDescription('Sensory controls');

		describeArgumentsForQuery(sensorCommand.addCommand('on', function(req, res) {
			getSensorsForQuery(req, res).forEach(function(sensor) {
				if(sensor.element.classList.contains('sensor--started'))
					return res.error('Sensor "'+sensor.id+'" is already started');

				res.log('Engaging sensor "'+sensor.id+'".');
				sensor.delayedStart();
			});
		}).addDescription('Engage one or more sensors'));

		describeArgumentsForQuery(sensorCommand.addCommand('off', function(req, res) {
			getSensorsForQuery(req, res).forEach(function(sensor) {
				if(!sensor.element.classList.contains('sensor--started'))
					return res.error('Sensor "'+sensor.id+'" is not active');

				res.log('Disengaging sensor "'+sensor.id+'".');
				sensor.stop();
			});
		}).addDescription('Disengage one or more sensors'));

		describeArgumentsForQuery(sensorCommand.addCommand('toggle', function(req, res) {
			getSensorsForQuery(req, res).forEach(function(sensor) {
				if(sensor.element.classList.contains('sensor--started')) {
					res.log('Disengaging sensor "'+sensor.id+'".');
					sensor.stop();
				} else {
					res.log('Engaging sensor "'+sensor.id+'".');
					sensor.delayedStart();
				}
			});
		}).addDescription('Switch on/off for one or more sensors'));

		sensorCommand.addCommand('list', function(req, res) {
			app.sensor.list().forEach(function(sensor, i) {
				i > 0 && res.log('---');
				//res.debug('bus0'+i+': ', sensor.getSummary());
				res.keyValue('id', sensor.id);
				res.keyValue('status', (sensor.isActive() ? 'enabled ' : 'disabled') + '\t' + [
					'<a command="sensors on --sensor '+sensor.id+'">on</a>',
					'<a command="sensors off --sensor '+sensor.id+'">off</a>',
					'<a command="sensors toggle --sensor '+sensor.id+'">toggle</a>'
				].join(' '));
			});
		});
	};
});
;(function(){

/**
 * Require the given path.
 *
 * @param {String} path
 * @return {Object} exports
 * @api public
 */

function require(path, parent, orig) {
  var resolved = require.resolve(path);

  // lookup failed
  if (null == resolved) {
    orig = orig || path;
    parent = parent || 'root';
    var err = new Error('Failed to require "' + orig + '" from "' + parent + '"');
    err.path = orig;
    err.parent = parent;
    err.require = true;
    throw err;
  }

  var module = require.modules[resolved];

  // perform real require()
  // by invoking the module's
  // registered function
  if (!module._resolving && !module.exports) {
    var mod = {};
    mod.exports = {};
    mod.client = mod.component = true;
    module._resolving = true;
    module.call(this, mod.exports, require.relative(resolved), mod);
    delete module._resolving;
    module.exports = mod.exports;
  }

  return module.exports;
}

/**
 * Registered modules.
 */

require.modules = {};

/**
 * Registered aliases.
 */

require.aliases = {};

/**
 * Resolve `path`.
 *
 * Lookup:
 *
 *   - PATH/index.js
 *   - PATH.js
 *   - PATH
 *
 * @param {String} path
 * @return {String} path or null
 * @api private
 */

require.resolve = function(path) {
  if (path.charAt(0) === '/') path = path.slice(1);

  var paths = [
    path,
    path + '.js',
    path + '.json',
    path + '/index.js',
    path + '/index.json'
  ];

  for (var i = 0; i < paths.length; i++) {
    var path = paths[i];
    if (require.modules.hasOwnProperty(path)) return path;
    if (require.aliases.hasOwnProperty(path)) return require.aliases[path];
  }
};

/**
 * Normalize `path` relative to the current path.
 *
 * @param {String} curr
 * @param {String} path
 * @return {String}
 * @api private
 */

require.normalize = function(curr, path) {
  var segs = [];

  if ('.' != path.charAt(0)) return path;

  curr = curr.split('/');
  path = path.split('/');

  for (var i = 0; i < path.length; ++i) {
    if ('..' == path[i]) {
      curr.pop();
    } else if ('.' != path[i] && '' != path[i]) {
      segs.push(path[i]);
    }
  }

  return curr.concat(segs).join('/');
};

/**
 * Register module at `path` with callback `definition`.
 *
 * @param {String} path
 * @param {Function} definition
 * @api private
 */

require.register = function(path, definition) {
  require.modules[path] = definition;
};

/**
 * Alias a module definition.
 *
 * @param {String} from
 * @param {String} to
 * @api private
 */

require.alias = function(from, to) {
  if (!require.modules.hasOwnProperty(from)) {
    throw new Error('Failed to alias "' + from + '", it does not exist');
  }
  require.aliases[to] = from;
};

/**
 * Return a require function relative to the `parent` path.
 *
 * @param {String} parent
 * @return {Function}
 * @api private
 */

require.relative = function(parent) {
  var p = require.normalize(parent, '..');

  /**
   * lastIndexOf helper.
   */

  function lastIndexOf(arr, obj) {
    var i = arr.length;
    while (i--) {
      if (arr[i] === obj) return i;
    }
    return -1;
  }

  /**
   * The relative require() itself.
   */

  function localRequire(path) {
    var resolved = localRequire.resolve(path);
    return require(resolved, parent, path);
  }

  /**
   * Resolve relative to the parent.
   */

  localRequire.resolve = function(path) {
    var c = path.charAt(0);
    if ('/' == c) return path.slice(1);
    if ('.' == c) return require.normalize(p, path);

    // resolve deps by returning
    // the dep in the nearest "deps"
    // directory
    var segs = parent.split('/');
    var i = lastIndexOf(segs, 'deps') + 1;
    if (!i) i = 0;
    path = segs.slice(0, i + 1).join('/') + '/deps/' + path;
    return path;
  };

  /**
   * Check if module is defined at `path`.
   */

  localRequire.exists = function(path) {
    return require.modules.hasOwnProperty(localRequire.resolve(path));
  };

  return localRequire;
};
require.register("component-emitter/index.js", function(exports, require, module){

/**
 * Expose `Emitter`.
 */

module.exports = Emitter;

/**
 * Initialize a new `Emitter`.
 *
 * @api public
 */

function Emitter(obj) {
  if (obj) return mixin(obj);
};

/**
 * Mixin the emitter properties.
 *
 * @param {Object} obj
 * @return {Object}
 * @api private
 */

function mixin(obj) {
  for (var key in Emitter.prototype) {
    obj[key] = Emitter.prototype[key];
  }
  return obj;
}

/**
 * Listen on the given `event` with `fn`.
 *
 * @param {String} event
 * @param {Function} fn
 * @return {Emitter}
 * @api public
 */

Emitter.prototype.on =
Emitter.prototype.addEventListener = function(event, fn){
  this._callbacks = this._callbacks || {};
  (this._callbacks[event] = this._callbacks[event] || [])
    .push(fn);
  return this;
};

/**
 * Adds an `event` listener that will be invoked a single
 * time then automatically removed.
 *
 * @param {String} event
 * @param {Function} fn
 * @return {Emitter}
 * @api public
 */

Emitter.prototype.once = function(event, fn){
  var self = this;
  this._callbacks = this._callbacks || {};

  function on() {
    self.off(event, on);
    fn.apply(this, arguments);
  }

  on.fn = fn;
  this.on(event, on);
  return this;
};

/**
 * Remove the given callback for `event` or all
 * registered callbacks.
 *
 * @param {String} event
 * @param {Function} fn
 * @return {Emitter}
 * @api public
 */

Emitter.prototype.off =
Emitter.prototype.removeListener =
Emitter.prototype.removeAllListeners =
Emitter.prototype.removeEventListener = function(event, fn){
  this._callbacks = this._callbacks || {};

  // all
  if (0 == arguments.length) {
    this._callbacks = {};
    return this;
  }

  // specific event
  var callbacks = this._callbacks[event];
  if (!callbacks) return this;

  // remove all handlers
  if (1 == arguments.length) {
    delete this._callbacks[event];
    return this;
  }

  // remove specific handler
  var cb;
  for (var i = 0; i < callbacks.length; i++) {
    cb = callbacks[i];
    if (cb === fn || cb.fn === fn) {
      callbacks.splice(i, 1);
      break;
    }
  }
  return this;
};

/**
 * Emit `event` with the given args.
 *
 * @param {String} event
 * @param {Mixed} ...
 * @return {Emitter}
 */

Emitter.prototype.emit = function(event){
  this._callbacks = this._callbacks || {};
  var args = [].slice.call(arguments, 1)
    , callbacks = this._callbacks[event];

  if (callbacks) {
    callbacks = callbacks.slice(0);
    for (var i = 0, len = callbacks.length; i < len; ++i) {
      callbacks[i].apply(this, args);
    }
  }

  return this;
};

/**
 * Return array of callbacks for `event`.
 *
 * @param {String} event
 * @return {Array}
 * @api public
 */

Emitter.prototype.listeners = function(event){
  this._callbacks = this._callbacks || {};
  return this._callbacks[event] || [];
};

/**
 * Check if this emitter has `event` handlers.
 *
 * @param {String} event
 * @return {Boolean}
 * @api public
 */

Emitter.prototype.hasListeners = function(event){
  return !! this.listeners(event).length;
};

});
require.register("component-reduce/index.js", function(exports, require, module){

/**
 * Reduce `arr` with `fn`.
 *
 * @param {Array} arr
 * @param {Function} fn
 * @param {Mixed} initial
 *
 * TODO: combatible error handling?
 */

module.exports = function(arr, fn, initial){
  var idx = 0;
  var len = arr.length;
  var curr = arguments.length == 3
    ? initial
    : arr[idx++];

  while (idx < len) {
    curr = fn.call(null, curr, arr[idx], ++idx, arr);
  }

  return curr;
};
});
require.register("superagent/lib/client.js", function(exports, require, module){
/**
 * Module dependencies.
 */

var Emitter = require('emitter');
var reduce = require('reduce');

/**
 * Root reference for iframes.
 */

var root = 'undefined' == typeof window
  ? this
  : window;

/**
 * Noop.
 */

function noop(){};

/**
 * Check if `obj` is a host object,
 * we don't want to serialize these :)
 *
 * TODO: future proof, move to compoent land
 *
 * @param {Object} obj
 * @return {Boolean}
 * @api private
 */

function isHost(obj) {
  var str = {}.toString.call(obj);

  switch (str) {
    case '[object File]':
    case '[object Blob]':
    case '[object FormData]':
      return true;
    default:
      return false;
  }
}

/**
 * Determine XHR.
 */

function getXHR() {
  if (root.XMLHttpRequest
    && ('file:' != root.location.protocol || !root.ActiveXObject)) {
    return new XMLHttpRequest;
  } else {
    try { return new ActiveXObject('Microsoft.XMLHTTP'); } catch(e) {}
    try { return new ActiveXObject('Msxml2.XMLHTTP.6.0'); } catch(e) {}
    try { return new ActiveXObject('Msxml2.XMLHTTP.3.0'); } catch(e) {}
    try { return new ActiveXObject('Msxml2.XMLHTTP'); } catch(e) {}
  }
  return false;
}

/**
 * Removes leading and trailing whitespace, added to support IE.
 *
 * @param {String} s
 * @return {String}
 * @api private
 */

var trim = ''.trim
  ? function(s) { return s.trim(); }
  : function(s) { return s.replace(/(^\s*|\s*$)/g, ''); };

/**
 * Check if `obj` is an object.
 *
 * @param {Object} obj
 * @return {Boolean}
 * @api private
 */

function isObject(obj) {
  return obj === Object(obj);
}

/**
 * Serialize the given `obj`.
 *
 * @param {Object} obj
 * @return {String}
 * @api private
 */

function serialize(obj) {
  if (!isObject(obj)) return obj;
  var pairs = [];
  for (var key in obj) {
    if (null != obj[key]) {
      pairs.push(encodeURIComponent(key)
        + '=' + encodeURIComponent(obj[key]));
    }
  }
  return pairs.join('&');
}

/**
 * Expose serialization method.
 */

 request.serializeObject = serialize;

 /**
  * Parse the given x-www-form-urlencoded `str`.
  *
  * @param {String} str
  * @return {Object}
  * @api private
  */

function parseString(str) {
  var obj = {};
  var pairs = str.split('&');
  var parts;
  var pair;

  for (var i = 0, len = pairs.length; i < len; ++i) {
    pair = pairs[i];
    parts = pair.split('=');
    obj[decodeURIComponent(parts[0])] = decodeURIComponent(parts[1]);
  }

  return obj;
}

/**
 * Expose parser.
 */

request.parseString = parseString;

/**
 * Default MIME type map.
 *
 *     superagent.types.xml = 'application/xml';
 *
 */

request.types = {
  html: 'text/html',
  json: 'application/json',
  xml: 'application/xml',
  urlencoded: 'application/x-www-form-urlencoded',
  'form': 'application/x-www-form-urlencoded',
  'form-data': 'application/x-www-form-urlencoded'
};

/**
 * Default serialization map.
 *
 *     superagent.serialize['application/xml'] = function(obj){
 *       return 'generated xml here';
 *     };
 *
 */

 request.serialize = {
   'application/x-www-form-urlencoded': serialize,
   'application/json': JSON.stringify
 };

 /**
  * Default parsers.
  *
  *     superagent.parse['application/xml'] = function(str){
  *       return { object parsed from str };
  *     };
  *
  */

request.parse = {
  'application/x-www-form-urlencoded': parseString,
  'application/json': JSON.parse
};

/**
 * Parse the given header `str` into
 * an object containing the mapped fields.
 *
 * @param {String} str
 * @return {Object}
 * @api private
 */

function parseHeader(str) {
  var lines = str.split(/\r?\n/);
  var fields = {};
  var index;
  var line;
  var field;
  var val;

  lines.pop(); // trailing CRLF

  for (var i = 0, len = lines.length; i < len; ++i) {
    line = lines[i];
    index = line.indexOf(':');
    field = line.slice(0, index).toLowerCase();
    val = trim(line.slice(index + 1));
    fields[field] = val;
  }

  return fields;
}

/**
 * Return the mime type for the given `str`.
 *
 * @param {String} str
 * @return {String}
 * @api private
 */

function type(str){
  return str.split(/ *; */).shift();
};

/**
 * Return header field parameters.
 *
 * @param {String} str
 * @return {Object}
 * @api private
 */

function params(str){
  return reduce(str.split(/ *; */), function(obj, str){
    var parts = str.split(/ *= */)
      , key = parts.shift()
      , val = parts.shift();

    if (key && val) obj[key] = val;
    return obj;
  }, {});
};

/**
 * Initialize a new `Response` with the given `xhr`.
 *
 *  - set flags (.ok, .error, etc)
 *  - parse header
 *
 * Examples:
 *
 *  Aliasing `superagent` as `request` is nice:
 *
 *      request = superagent;
 *
 *  We can use the promise-like API, or pass callbacks:
 *
 *      request.get('/').end(function(res){});
 *      request.get('/', function(res){});
 *
 *  Sending data can be chained:
 *
 *      request
 *        .post('/user')
 *        .send({ name: 'tj' })
 *        .end(function(res){});
 *
 *  Or passed to `.send()`:
 *
 *      request
 *        .post('/user')
 *        .send({ name: 'tj' }, function(res){});
 *
 *  Or passed to `.post()`:
 *
 *      request
 *        .post('/user', { name: 'tj' })
 *        .end(function(res){});
 *
 * Or further reduced to a single call for simple cases:
 *
 *      request
 *        .post('/user', { name: 'tj' }, function(res){});
 *
 * @param {XMLHTTPRequest} xhr
 * @param {Object} options
 * @api private
 */

function Response(req, options) {
  options = options || {};
  this.req = req;
  this.xhr = this.req.xhr;
  this.text = this.req.method !='HEAD'
     ? this.xhr.responseText
     : null;
  this.setStatusProperties(this.xhr.status);
  this.header = this.headers = parseHeader(this.xhr.getAllResponseHeaders());
  // getAllResponseHeaders sometimes falsely returns "" for CORS requests, but
  // getResponseHeader still works. so we get content-type even if getting
  // other headers fails.
  this.header['content-type'] = this.xhr.getResponseHeader('content-type');
  this.setHeaderProperties(this.header);
  this.body = this.req.method != 'HEAD'
    ? this.parseBody(this.text)
    : null;
}

/**
 * Get case-insensitive `field` value.
 *
 * @param {String} field
 * @return {String}
 * @api public
 */

Response.prototype.get = function(field){
  return this.header[field.toLowerCase()];
};

/**
 * Set header related properties:
 *
 *   - `.type` the content type without params
 *
 * A response of "Content-Type: text/plain; charset=utf-8"
 * will provide you with a `.type` of "text/plain".
 *
 * @param {Object} header
 * @api private
 */

Response.prototype.setHeaderProperties = function(header){
  // content-type
  var ct = this.header['content-type'] || '';
  this.type = type(ct);

  // params
  var obj = params(ct);
  for (var key in obj) this[key] = obj[key];
};

/**
 * Parse the given body `str`.
 *
 * Used for auto-parsing of bodies. Parsers
 * are defined on the `superagent.parse` object.
 *
 * @param {String} str
 * @return {Mixed}
 * @api private
 */

Response.prototype.parseBody = function(str){
  var parse = request.parse[this.type];
  return parse && str && str.length
    ? parse(str)
    : null;
};

/**
 * Set flags such as `.ok` based on `status`.
 *
 * For example a 2xx response will give you a `.ok` of __true__
 * whereas 5xx will be __false__ and `.error` will be __true__. The
 * `.clientError` and `.serverError` are also available to be more
 * specific, and `.statusType` is the class of error ranging from 1..5
 * sometimes useful for mapping respond colors etc.
 *
 * "sugar" properties are also defined for common cases. Currently providing:
 *
 *   - .noContent
 *   - .badRequest
 *   - .unauthorized
 *   - .notAcceptable
 *   - .notFound
 *
 * @param {Number} status
 * @api private
 */

Response.prototype.setStatusProperties = function(status){
  var type = status / 100 | 0;

  // status / class
  this.status = status;
  this.statusType = type;

  // basics
  this.info = 1 == type;
  this.ok = 2 == type;
  this.clientError = 4 == type;
  this.serverError = 5 == type;
  this.error = (4 == type || 5 == type)
    ? this.toError()
    : false;

  // sugar
  this.accepted = 202 == status;
  this.noContent = 204 == status || 1223 == status;
  this.badRequest = 400 == status;
  this.unauthorized = 401 == status;
  this.notAcceptable = 406 == status;
  this.notFound = 404 == status;
  this.forbidden = 403 == status;
};

/**
 * Return an `Error` representative of this response.
 *
 * @return {Error}
 * @api public
 */

Response.prototype.toError = function(){
  var req = this.req;
  var method = req.method;
  var url = req.url;

  var msg = 'cannot ' + method + ' ' + url + ' (' + this.status + ')';
  var err = new Error(msg);
  err.status = this.status;
  err.method = method;
  err.url = url;

  return err;
};

/**
 * Expose `Response`.
 */

request.Response = Response;

/**
 * Initialize a new `Request` with the given `method` and `url`.
 *
 * @param {String} method
 * @param {String} url
 * @api public
 */

function Request(method, url) {
  var self = this;
  Emitter.call(this);
  this._query = this._query || [];
  this.method = method;
  this.url = url;
  this.header = {};
  this._header = {};
  this.on('end', function(){
    var err = null;
    var res = null;

    try {
      res = new Response(self);
    } catch(e) {
      err = new Error('Parser is unable to parse the response');
      err.parse = true;
      err.original = e;
    }

    self.callback(err, res);
  });
}

/**
 * Mixin `Emitter`.
 */

Emitter(Request.prototype);

/**
 * Allow for extension
 */

Request.prototype.use = function(fn) {
  fn(this);
  return this;
}

/**
 * Set timeout to `ms`.
 *
 * @param {Number} ms
 * @return {Request} for chaining
 * @api public
 */

Request.prototype.timeout = function(ms){
  this._timeout = ms;
  return this;
};

/**
 * Clear previous timeout.
 *
 * @return {Request} for chaining
 * @api public
 */

Request.prototype.clearTimeout = function(){
  this._timeout = 0;
  clearTimeout(this._timer);
  return this;
};

/**
 * Abort the request, and clear potential timeout.
 *
 * @return {Request}
 * @api public
 */

Request.prototype.abort = function(){
  if (this.aborted) return;
  this.aborted = true;
  this.xhr.abort();
  this.clearTimeout();
  this.emit('abort');
  return this;
};

/**
 * Set header `field` to `val`, or multiple fields with one object.
 *
 * Examples:
 *
 *      req.get('/')
 *        .set('Accept', 'application/json')
 *        .set('X-API-Key', 'foobar')
 *        .end(callback);
 *
 *      req.get('/')
 *        .set({ Accept: 'application/json', 'X-API-Key': 'foobar' })
 *        .end(callback);
 *
 * @param {String|Object} field
 * @param {String} val
 * @return {Request} for chaining
 * @api public
 */

Request.prototype.set = function(field, val){
  if (isObject(field)) {
    for (var key in field) {
      this.set(key, field[key]);
    }
    return this;
  }
  this._header[field.toLowerCase()] = val;
  this.header[field] = val;
  return this;
};

/**
 * Remove header `field`.
 *
 * Example:
 *
 *      req.get('/')
 *        .unset('User-Agent')
 *        .end(callback);
 *
 * @param {String} field
 * @return {Request} for chaining
 * @api public
 */

Request.prototype.unset = function(field){
  delete this._header[field.toLowerCase()];
  delete this.header[field];
  return this;
};

/**
 * Get case-insensitive header `field` value.
 *
 * @param {String} field
 * @return {String}
 * @api private
 */

Request.prototype.getHeader = function(field){
  return this._header[field.toLowerCase()];
};

/**
 * Set Content-Type to `type`, mapping values from `request.types`.
 *
 * Examples:
 *
 *      superagent.types.xml = 'application/xml';
 *
 *      request.post('/')
 *        .type('xml')
 *        .send(xmlstring)
 *        .end(callback);
 *
 *      request.post('/')
 *        .type('application/xml')
 *        .send(xmlstring)
 *        .end(callback);
 *
 * @param {String} type
 * @return {Request} for chaining
 * @api public
 */

Request.prototype.type = function(type){
  this.set('Content-Type', request.types[type] || type);
  return this;
};

/**
 * Set Accept to `type`, mapping values from `request.types`.
 *
 * Examples:
 *
 *      superagent.types.json = 'application/json';
 *
 *      request.get('/agent')
 *        .accept('json')
 *        .end(callback);
 *
 *      request.get('/agent')
 *        .accept('application/json')
 *        .end(callback);
 *
 * @param {String} accept
 * @return {Request} for chaining
 * @api public
 */

Request.prototype.accept = function(type){
  this.set('Accept', request.types[type] || type);
  return this;
};

/**
 * Set Authorization field value with `user` and `pass`.
 *
 * @param {String} user
 * @param {String} pass
 * @return {Request} for chaining
 * @api public
 */

Request.prototype.auth = function(user, pass){
  var str = btoa(user + ':' + pass);
  this.set('Authorization', 'Basic ' + str);
  return this;
};

/**
* Add query-string `val`.
*
* Examples:
*
*   request.get('/shoes')
*     .query('size=10')
*     .query({ color: 'blue' })
*
* @param {Object|String} val
* @return {Request} for chaining
* @api public
*/

Request.prototype.query = function(val){
  if ('string' != typeof val) val = serialize(val);
  if (val) this._query.push(val);
  return this;
};

/**
 * Write the field `name` and `val` for "multipart/form-data"
 * request bodies.
 *
 * ``` js
 * request.post('/upload')
 *   .field('foo', 'bar')
 *   .end(callback);
 * ```
 *
 * @param {String} name
 * @param {String|Blob|File} val
 * @return {Request} for chaining
 * @api public
 */

Request.prototype.field = function(name, val){
  if (!this._formData) this._formData = new FormData();
  this._formData.append(name, val);
  return this;
};

/**
 * Queue the given `file` as an attachment to the specified `field`,
 * with optional `filename`.
 *
 * ``` js
 * request.post('/upload')
 *   .attach(new Blob(['<a id="a"><b id="b">hey!</b></a>'], { type: "text/html"}))
 *   .end(callback);
 * ```
 *
 * @param {String} field
 * @param {Blob|File} file
 * @param {String} filename
 * @return {Request} for chaining
 * @api public
 */

Request.prototype.attach = function(field, file, filename){
  if (!this._formData) this._formData = new FormData();
  this._formData.append(field, file, filename);
  return this;
};

/**
 * Send `data`, defaulting the `.type()` to "json" when
 * an object is given.
 *
 * Examples:
 *
 *       // querystring
 *       request.get('/search')
 *         .end(callback)
 *
 *       // multiple data "writes"
 *       request.get('/search')
 *         .send({ search: 'query' })
 *         .send({ range: '1..5' })
 *         .send({ order: 'desc' })
 *         .end(callback)
 *
 *       // manual json
 *       request.post('/user')
 *         .type('json')
 *         .send('{"name":"tj"})
 *         .end(callback)
 *
 *       // auto json
 *       request.post('/user')
 *         .send({ name: 'tj' })
 *         .end(callback)
 *
 *       // manual x-www-form-urlencoded
 *       request.post('/user')
 *         .type('form')
 *         .send('name=tj')
 *         .end(callback)
 *
 *       // auto x-www-form-urlencoded
 *       request.post('/user')
 *         .type('form')
 *         .send({ name: 'tj' })
 *         .end(callback)
 *
 *       // defaults to x-www-form-urlencoded
  *      request.post('/user')
  *        .send('name=tobi')
  *        .send('species=ferret')
  *        .end(callback)
 *
 * @param {String|Object} data
 * @return {Request} for chaining
 * @api public
 */

Request.prototype.send = function(data){
  var obj = isObject(data);
  var type = this.getHeader('Content-Type');

  // merge
  if (obj && isObject(this._data)) {
    for (var key in data) {
      this._data[key] = data[key];
    }
  } else if ('string' == typeof data) {
    if (!type) this.type('form');
    type = this.getHeader('Content-Type');
    if ('application/x-www-form-urlencoded' == type) {
      this._data = this._data
        ? this._data + '&' + data
        : data;
    } else {
      this._data = (this._data || '') + data;
    }
  } else {
    this._data = data;
  }

  if (!obj) return this;
  if (!type) this.type('json');
  return this;
};

/**
 * Invoke the callback with `err` and `res`
 * and handle arity check.
 *
 * @param {Error} err
 * @param {Response} res
 * @api private
 */

Request.prototype.callback = function(err, res){
  var fn = this._callback;
  this.clearTimeout();
  if (2 == fn.length) return fn(err, res);
  if (err) return this.emit('error', err);
  fn(res);
};

/**
 * Invoke callback with x-domain error.
 *
 * @api private
 */

Request.prototype.crossDomainError = function(){
  var err = new Error('Origin is not allowed by Access-Control-Allow-Origin');
  err.crossDomain = true;
  this.callback(err);
};

/**
 * Invoke callback with timeout error.
 *
 * @api private
 */

Request.prototype.timeoutError = function(){
  var timeout = this._timeout;
  var err = new Error('timeout of ' + timeout + 'ms exceeded');
  err.timeout = timeout;
  this.callback(err);
};

/**
 * Enable transmission of cookies with x-domain requests.
 *
 * Note that for this to work the origin must not be
 * using "Access-Control-Allow-Origin" with a wildcard,
 * and also must set "Access-Control-Allow-Credentials"
 * to "true".
 *
 * @api public
 */

Request.prototype.withCredentials = function(){
  this._withCredentials = true;
  return this;
};

/**
 * Initiate request, invoking callback `fn(res)`
 * with an instanceof `Response`.
 *
 * @param {Function} fn
 * @return {Request} for chaining
 * @api public
 */

Request.prototype.end = function(fn){
  var self = this;
  var xhr = this.xhr = getXHR();
  var query = this._query.join('&');
  var timeout = this._timeout;
  var data = this._formData || this._data;

  // store callback
  this._callback = fn || noop;

  // state change
  xhr.onreadystatechange = function(){
    if (4 != xhr.readyState) return;
    if (0 == xhr.status) {
      if (self.aborted) return self.timeoutError();
      return self.crossDomainError();
    }
    self.emit('end');
  };

  // progress
  if (xhr.upload) {
    xhr.upload.onprogress = function(e){
      e.percent = e.loaded / e.total * 100;
      self.emit('progress', e);
    };
  }

  // timeout
  if (timeout && !this._timer) {
    this._timer = setTimeout(function(){
      self.abort();
    }, timeout);
  }

  // querystring
  if (query) {
    query = request.serializeObject(query);
    this.url += ~this.url.indexOf('?')
      ? '&' + query
      : '?' + query;
  }

  // initiate request
  xhr.open(this.method, this.url, true);

  // CORS
  if (this._withCredentials) xhr.withCredentials = true;

  // body
  if ('GET' != this.method && 'HEAD' != this.method && 'string' != typeof data && !isHost(data)) {
    // serialize stuff
    var serialize = request.serialize[this.getHeader('Content-Type')];
    if (serialize) data = serialize(data);
  }

  // set header fields
  for (var field in this.header) {
    if (null == this.header[field]) continue;
    xhr.setRequestHeader(field, this.header[field]);
  }

  // send stuff
  this.emit('request', this);
  xhr.send(data);
  return this;
};

/**
 * Expose `Request`.
 */

request.Request = Request;

/**
 * Issue a request:
 *
 * Examples:
 *
 *    request('GET', '/users').end(callback)
 *    request('/users').end(callback)
 *    request('/users', callback)
 *
 * @param {String} method
 * @param {String|Function} url or callback
 * @return {Request}
 * @api public
 */

function request(method, url) {
  // callback
  if ('function' == typeof url) {
    return new Request('GET', method).end(url);
  }

  // url first
  if (1 == arguments.length) {
    return new Request('GET', method);
  }

  return new Request(method, url);
}

/**
 * GET `url` with optional callback `fn(res)`.
 *
 * @param {String} url
 * @param {Mixed|Function} data or fn
 * @param {Function} fn
 * @return {Request}
 * @api public
 */

request.get = function(url, data, fn){
  var req = request('GET', url);
  if ('function' == typeof data) fn = data, data = null;
  if (data) req.query(data);
  if (fn) req.end(fn);
  return req;
};

/**
 * HEAD `url` with optional callback `fn(res)`.
 *
 * @param {String} url
 * @param {Mixed|Function} data or fn
 * @param {Function} fn
 * @return {Request}
 * @api public
 */

request.head = function(url, data, fn){
  var req = request('HEAD', url);
  if ('function' == typeof data) fn = data, data = null;
  if (data) req.send(data);
  if (fn) req.end(fn);
  return req;
};

/**
 * DELETE `url` with optional callback `fn(res)`.
 *
 * @param {String} url
 * @param {Function} fn
 * @return {Request}
 * @api public
 */

request.del = function(url, fn){
  var req = request('DELETE', url);
  if (fn) req.end(fn);
  return req;
};

/**
 * PATCH `url` with optional `data` and callback `fn(res)`.
 *
 * @param {String} url
 * @param {Mixed} data
 * @param {Function} fn
 * @return {Request}
 * @api public
 */

request.patch = function(url, data, fn){
  var req = request('PATCH', url);
  if ('function' == typeof data) fn = data, data = null;
  if (data) req.send(data);
  if (fn) req.end(fn);
  return req;
};

/**
 * POST `url` with optional `data` and callback `fn(res)`.
 *
 * @param {String} url
 * @param {Mixed} data
 * @param {Function} fn
 * @return {Request}
 * @api public
 */

request.post = function(url, data, fn){
  var req = request('POST', url);
  if ('function' == typeof data) fn = data, data = null;
  if (data) req.send(data);
  if (fn) req.end(fn);
  return req;
};

/**
 * PUT `url` with optional `data` and callback `fn(res)`.
 *
 * @param {String} url
 * @param {Mixed|Function} data or fn
 * @param {Function} fn
 * @return {Request}
 * @api public
 */

request.put = function(url, data, fn){
  var req = request('PUT', url);
  if ('function' == typeof data) fn = data, data = null;
  if (data) req.send(data);
  if (fn) req.end(fn);
  return req;
};

/**
 * Expose `request`.
 */

module.exports = request;

});




require.alias("component-emitter/index.js", "superagent/deps/emitter/index.js");
require.alias("component-emitter/index.js", "emitter/index.js");

require.alias("component-reduce/index.js", "superagent/deps/reduce/index.js");
require.alias("component-reduce/index.js", "reduce/index.js");

require.alias("superagent/lib/client.js", "superagent/index.js");if (typeof exports == "object") {
  module.exports = require("superagent");
} else if (typeof define == "function" && define.amd) {
  define('superagent',[], function(){ return require("superagent"); });
} else {
  this["superagent"] = require("superagent");
}})();
define('portfolio-manager/items/Item',[], function() {

	function quickHash(str) {
		var hash = 0;
		if (str.length == 0) return hash;
		for (var i = 0; i < str.length; i++) {
			char = str.charCodeAt(i);
			hash = ((hash<<5)-hash)+char;
			hash = hash & hash; // Convert to 32bit integer
		}
		return hash;
	}

	function Item (info) {
		this.id = null;
		Object.keys(info).forEach(function(key) {
			this[key] = info[key];
		}.bind(this));

		if(!this.id)
			this.generateId();
	}

	Item.prototype.generateId = function() {
		// Make up an ID
		this.id = (this.name.replace(/\W+/g, '').substr(0,4) + '-' + quickHash(this.name).toString(36).replace(/\W+/g, '').substr(0,3))
			.toLowerCase();
	};

	/**
	 * @returns Promise
	 */
	Item.prototype.get = function () {
		throw new Error('Not implemented.');
	};

	// Is in fact a controller
	Item.prototype.create = function (req, res) {

		res.header(this.name);
		res.log(this.name.toUpperCase() + ' (type: '+this.type+')');
		res.log('------------------------------------');

		Object.keys(this).forEach(function(key) {
			var value = this[key];
			switch (typeof value) {
				case 'string':
				case 'number':
					res.keyValue(key, value);
				default:
					return;
			}
		}.bind(this));

	};

	Item.prototype.destroy = function() {
		throw new Error('Not implemented.');
	};


	return Item;
});
define('portfolio-manager/items/GithubItem',[
	'promise',
	'superagent',
	'base64',
	'markdown',

	'window-manager',

	'./Item'
], function(
	Promise,
	superagent,
	base64,
	markdown,

	$window,

	Item) {

	var SEP = '\t';

	function GithubItem (info) {
		Item.call(this, info);

		this.githost = this.repository.substring(
				this.repository.indexOf('@') + 1,
			this.repository.indexOf(':')
		);
		this.username = this.repository.substring(
			this.repository.indexOf(':') + 1,
			this.repository.indexOf('/')
		);
		this.reponame = this.repository.substring(
			this.repository.indexOf('/') + 1,
			this.repository.length - 4
		);
		this.url = '<a href="https://'+this.githost+'/'+this.username+ '/' +this.reponame+'" target="_blank">'+this.githost+'/'+this.username+ '/' +this.reponame+'</a>';
		this.window = null;
	}

	GithubItem.prototype = Object.create(Item.prototype);
	GithubItem.prototype.constructor = GithubItem;

	GithubItem.prototype.get = function () {
		return this.getEndpoint();
	};

	GithubItem.prototype.getEndpoint = function () {
		var args = arguments,
			pieces = Object.keys(args).map(function(n) {
			return args[n];
		});

		pieces.unshift(this.reponame);
		pieces.unshift(this.username);

		return new Promise(function(resolve, reject) {
			superagent.get('https://api.github.com/repos/'+pieces.join('/'), function(result) {
				if(!result.ok) {
					return reject(result.error);
				}
				resolve(result.body);
			});
		}.bind(this));
	};

	GithubItem.prototype.getReadme = function() {
		throw new Error('Item has no README');
	};
	// Is in fact a controller
	GithubItem.prototype.create = function (req, res) {
		Item.prototype.create.apply(this, arguments);
		res.log();
		res.log('Downloading repository intel...');
		return this.get().then(function(summaryResponse) {
			res.log('Retrieved ' + (new Date()));
			res.log();
			res.log('GitHub info:');
			if(summaryResponse) {
				var summarized = {
					"Description": summaryResponse.description,
					"Created": summaryResponse.created_at,
					"Updated": summaryResponse.updated_at,
					"Pushed": summaryResponse.pushed_at,
					"Language": summaryResponse.language,
					"Default branch": summaryResponse.default_branch
				};

				Object.keys(summarized).forEach(function(key) {
					res.keyValue(key, summarized[key]);
				});
				res.log();
			} else {
				res.error('Github summary API could not be reached.');
			}

			if(this.readme) {

					this.temporaryMarkdownShit('README.md').then(function (readmeResponse) {

						res.log('Opening README.md in a new window...');
						this.window = new $window.MarkdownWindow(
							'md:' + this.id,
							this.name + '/ README.md',
							readmeResponse
						);
						res.onceQueueFlushed(function() {
							req.app.window.openNewWindow(this.window);
						}.bind(this));
					}.bind(this));

			} else {
				res.log('No README.md found');
			}
		}.bind(this)).catch(function(e) {
			res.error(e);
		});
	};

	GithubItem.prototype.destroy = function() {
		this.window.destroy();
	};

	GithubItem.prototype.temporaryMarkdownShit = function(file) {
		var dir = this.dir;
		return new Promise(function(resolve, reject) {
			superagent.get(require.toUrl('portfolio/' + dir + '/' + file), function(result) {
				if(!result.ok) {
					return reject(result.error);
				}
				resolve(result.text);
			});
		});
	};

	GithubItem.prototype.parseReadme = function (b64) {
		var element = document.createElement('div');
		element.classList.add('markdown');
		element.innerHTML = markdown.toHTML(
			b64
			//base64.decode(b64)
		);

		var nodeIterator = document.createNodeIterator(
			element,
			NodeFilter.SHOW_ELEMENT,
			function(node) {
				return !!node.getAttribute('src')
			}
		);

		var node;
		while ((node = nodeIterator.nextNode())) {
			var src = node.getAttribute('src'); // @TODO: hardcoded branch name, refer to branch in json
			if(src.indexOf('./') === 0) {
				node.setAttribute('src', [
					'https://raw.githubusercontent.com',
					this.username,
					this.reponame,
					this.branch,
					src.substr(2)
				].join('/'));
			}
		}

		return element;
	};

	return GithubItem;
});
define('portfolio-manager/items/ScriptItem',[
	'require',
	'promise',
	'window-manager',
	'./Item'
], function(
	require,
	Promise,
	$window,
	Item) {

	window.define = define;

	function ScriptItem (info) {
		Item.call(this, info);

		if(!this.script)
			throw new Error('ScriptItem needs a script name specified');
	}

	ScriptItem.prototype = Object.create(Item.prototype);
	ScriptItem.prototype.constructor = ScriptItem;

	ScriptItem.prototype.get = function () {
		return new Promise(function(resolve, reject) {
			require(['portfolio/'+this.script+'/src/main'], function(Script) {
				if(!Script) {
					return reject(new Error('Could not get script "'+this.script+'", for it is empty. Fucksake...'));
				}
				resolve(Script);
			}.bind(this));
		}.bind(this));
	};

	// Is in fact a controller
	ScriptItem.prototype.create = function (req, res) {
		Item.prototype.create.apply(this, arguments);

		res.log();
		res.log('Downloading script dependencies...');
		return this.get().then(function(Script) {
			if(this.instance)
				return res.error('Script item is already instantiated');

			res.debug('Executing script with ' + Object.keys(this.options).length + ' options', this.options);

			var instance = new Script(this.options),
				element = typeof instance.getElement === 'function' ? instance.getElement() : instance.element;

			this.instance = instance;

			if(element)
				this.window = new $window.BasicWindow(
					'js:' + this.id,
					this.name,
					element);

			this.window.addFlag('script');

			this.window.addDestroyCallback(function() {
				res.debug('Closing script window, send SIGTERM');
				this.destroy();
			}.bind(this));

			res.onceQueueFlushed(function() {
				req.app.window.openNewWindow(this.window);
			}.bind(this));

		}.bind(this)).catch(function(err) {
			res.error(err);
		});
	};

	ScriptItem.prototype.destroy = function() {
		this.instance.stop();
		delete this.instance;
	};

	return ScriptItem;
});
define('portfolio-manager/items/YoutubeItem',[
	//'youtubePlayer',
	'window-manager',

	'./Item'
], function(
	//youtubePlayer,
	$window,

	Item) {

	var SEP = '\t';

	function YoutubeItem (info) {
		Item.call(this, info);
		this.link = '<a href="https://www.youtube.com/watch?v='+this.youtube+'" target="_blank" title="Click to open the Youtube page for this video">youtube.com/watch?v='+this.youtube+'</a>';
	}

	YoutubeItem.prototype = Object.create(Item.prototype);
	YoutubeItem.prototype.constructor = YoutubeItem;

	YoutubeItem.prototype.get = function () {

	};

	// Is in fact a controller
	YoutubeItem.prototype.create = function (req, res) {
		Item.prototype.create.apply(this, arguments);
		res.log();
		res.log('Opening video in a new window');

		var video = document.createElement('iframe');
		video.setAttribute('width', 640);
		video.setAttribute('height', 480);
		video.setAttribute('src', '//www.youtube.com/embed/' + this.youtube);
		video.setAttribute('allowfullscreen', 'true');
		video.setAttribute('frameborder', 0);
		this.window = new $window.BasicWindow('yt:' + this.id, this.name, video);
		this.window.addFlag('video');
		this.window.isResizable = false;
		res.onceQueueFlushed(function() {
			req.app.window.openNewWindow(this.window);
		}.bind(this));
	};

	YoutubeItem.prototype.destroy = function() {
		this.window.destroy();
	};

	return YoutubeItem;
});
define('portfolio-manager/items/ImageItem',[
	'window-manager',

	'./Item'
], function(
	$window,

	Item) {

	var SEP = '\t';

	function ImageItem (info) {
		Item.call(this, info);

	}

	ImageItem.prototype = Object.create(Item.prototype);
	ImageItem.prototype.constructor = ImageItem;

	ImageItem.prototype.get = function () {

	};


	// Is in fact a controller
	ImageItem.prototype.create = function (req, res) {
		Item.prototype.create.apply(this, arguments);
		res.log();
		res.log('Opening new image gallery');

		this.window = new $window.ImageWindow('img:' + this.id, this.name, this.images.map(function(imageFile) {
			return this.dir + '/' + imageFile;
		}.bind(this)));

		res.onceQueueFlushed(function() {
			req.app.window.openNewWindow(this.window);
		}.bind(this));
	};

	ImageItem.prototype.destroy = function() {
		this.window.destroy();
	};

	return ImageItem;
});
define('portfolio-manager/PortfolioManager',[
	'promise',
	'object-store',
	'superagent',

	'./items/Item',
	'./items/GithubItem',
	'./items/ScriptItem',
	'./items/YoutubeItem',
	'./items/ImageItem'
], function(
	Promise,
	ObjectStore,
	superagent,

	Item,
	GithubItem,
	ScriptItem,
	YoutubeItem,
	ImageItem) {

	function PortfolioManager () {
		ObjectStore.call(this);
	}

	PortfolioManager.prototype = Object.create(ObjectStore.prototype);
	PortfolioManager.prototype.constructor = PortfolioManager;

	PortfolioManager.prototype.load = function() {

		return new Promise(function(resolve, reject) {
			if (this._objects)
				return resolve(this._objects);

			superagent.get(this.getUrlForPath('info.json'), function (result) {
				if (!result.ok) {
					reject(new Error('Could not initialize portfolio'));
				}

				this._objects = result.body.objects;

				resolve(this._objects);
			}.bind(this)).set('Accept', 'application/json').on('error', function (err) {
				console.error(err);
				reject(err);
			});

		}.bind(this)).then(function(objects) {
			this.readSummaries(objects);
		}.bind(this));
	};

	PortfolioManager.prototype.getUrlForPath = function(file) {
		return require.toUrl('portfolio/' + file);
	};

	PortfolioManager.prototype.getTextFromServer = function() {
		return new Promise(function(resolve, reject) {
			superagent.get(this.getUrlForPath(file), function(result) {
				if(!result.ok) {
					return reject(result.error);
				}
				resolve(result.text);
			});
		}.bind(this));
	};


	PortfolioManager.prototype.readSummaries = function(portfolioObjects) {
		portfolioObjects.forEach(function(portfolioObject) {
			this.set(this.castSummary(portfolioObject));
		}.bind(this));
	};

	PortfolioManager.prototype.castSummary = function (portfolioObject) {
		switch(portfolioObject.type) {
			case 'github':
				return new GithubItem(portfolioObject);
			case 'script':
				return new ScriptItem(portfolioObject);
			case 'image':
				return new ImageItem(portfolioObject);
			case 'youtube':
				return new YoutubeItem(portfolioObject);
			default:
				return new Item(portfolioObject);
		}
	};

	PortfolioManager.prototype.listTypes = function() {
		return this.list().reduce(function(types, portfolioObject) {
			if(!types.indexOf(portfolioObject.type)) {
				types.push(portfolioObject.type);
			}
		}, []);
	};

	PortfolioManager.prototype.listType = function(type) {
		return this.list().filter(function(portfolioObject) {
			return portfolioObject === type;
		});
	};


	PortfolioManager.prototype.openModule = function() {

	};

	return PortfolioManager;
});
define('portfolio-manager/main',[

	'./PortfolioManager'
], function(
	PortfolioManager
	) {
	return {
		PortfolioManager: PortfolioManager
	};
});
define('portfolio-manager', ['portfolio-manager/main'], function (main) { return main; });

define('portfolio-manager/commands/view',[], function () {
	var SEP = '\t';
	return function(app) {
		function getPortfolioItemForArguments(req) {
			return app.portfolio.get(req.route[1]);
		}

		app.command.addCommand('view', function(req, res) {
			if(!req.route[1])
				return viewListController.apply(this, arguments);
			return viewItemController.apply(this, arguments);
		})
			.addDescription('Portfolio')
			.addOption('search', 's', 'Search for portfolio items')
			.isGreedy();

		function viewItemController (req, res) {
			var item = getPortfolioItemForArguments(req);

			if(!item) {
				return res.error(new Error('No such portfolio item ("'+req.route[1]+'")'));
			}

			item.create(req,res);
		}

		function viewListController (req, res) {

			res.header('Portfolio');

			res.log('Sorted and unsorted works of multimedia.');

			var lastEnumeratedCategory = null,
				portfolioList = app.portfolio.list();


			if(req.options.search) {
				var search = new RegExp(req.options.search, "i");
				portfolioList = portfolioList.filter(function(item) {
					if(item.name && item.name.match(search))
						return true;
					if(item.description && item.description.match(search))
						return true;
					if(item.category && item.category.match(search))
						return true;
					return false;
				});
			}

			portfolioList = portfolioList.sort(function(a,b) {
				return a.category.toLowerCase() == b.category.toLowerCase() ? (
						a.name.toLowerCase() == b.name.toLowerCase() ? 0 : a.name.toLowerCase() < b.name.toLowerCase() ? -1 : 1
					) : a.category.toLowerCase() < b.category.toLowerCase() ? -1 : 1;
			});

			res.log();


			if(!portfolioList.length) {
				return res.error(new Error('No portfolio items found for this query ("'+req.options.search+'").'));
			}


			var licenses = {};
			portfolioList.forEach(function(item) {
				item.category != lastEnumeratedCategory && res.log();
				var itemHtmlString = '<a command="view '+item.id+'">'+item.id+'</a>\t"' + item.name + '"';
				res.keyValue(item.category == lastEnumeratedCategory ? null : item.category, itemHtmlString);
				lastEnumeratedCategory = item.category;
				licenses[item.id] = item.license || 'none/proprietary';
			});

			licenses._contact = 'wvbe (wybe@x-54.com)';

			res.log();

			res.debug('(c) me unless stated otherwise, various licenses, type <a command="who">who</a> or <a command="debug">debug</a> for more info.', licenses);
		}
	};



});
define('portfolio-manager/commands/bubble',[], function () {
	return function(app) {
		var bubbleCommand = app.command.addCommand('bubble', function (req, res) {
			res.log('Bubble script is booting up. You might want to check out <a command="help bubble">help bubble</a> to find out how to play with it.');
			getActiveBubble(req, res).then(function (bubble) {
				res.log('Bubble booted');
			})
		})
				.addDescription('Play around with '),
			bubbleConfigurables = ['node_size', 'radius_near', 'radius_far', 'radius_void', 'attraction_multiplier', 'attraction_power', 'repulsion_multiplier', 'repulsion_power', 'slowdown_multiplier', 'node_color', 'line_color', 'gravity'],
			bubbleShortConfigurables = ['s', 'N', 'F', 'V', 'a', 'A', 'p', 'P', 'v', 'c', 'C', 'g'];

		function getActiveBubble(req, res) {
			var item = app.portfolio.get('bubb-msk');

			if(!item.window || !item.instance) {
				res.log('Bubble requires to be started first, starting...');
				return item.create(req, res).then(function() {
					return item.instance;
				});
			}

			return new Promise(function(resolve) {
				return resolve(item.instance);
			});
		}

		function createConfigurationWindow(activeBubble, configurableProperties) {
			var configElement = document.createElement('div');

			Object.keys(configurableProperties).forEach(function (propertyKey) {
				var propertyConfig = configurableProperties[propertyKey];


			});
		}

		var bubbleConfigCommand = bubbleCommand.addCommand('config', function(req, res) {
			getActiveBubble(req, res).then(function(bubble) {
				res.log('Configuring bubble...');
				var newConfig = {};

				if (!Object.keys(req.options).length) {
					res.error(new Error('Nothing was updated because you did not specify any properties, type <a command="help bubble config">help bubble config</a> for info.'));
					return;
				}

				bubbleConfigurables.forEach(function(key) {
					if(req.options[key] === undefined)
						return;

					newConfig[key] = (''+parseFloat(req.options[key]) == req.options[key]) ? parseFloat(req.options[key]) : req.options[key];

					res.log('\t' + key + '\t' + newConfig[key]);
				});

				if (!Object.keys(newConfig).length) {
					res.error(new Error('No valid configuration properties specified, type <a command="help bubble config">help bubble config</a> for info.'));
					return;
				}

				bubble.reconfig(newConfig);
			});
		})
			.addDescription('Reconfigure parameters that define the bubble behaviour');

		bubbleConfigurables.forEach(function(opt, i) {
			bubbleConfigCommand.addOption(opt, bubbleShortConfigurables[i]);
		});

		bubbleCommand.addCommand('explode', function(req, res) {
			getActiveBubble(req, res).then(function(bubble) {
				var force = req.options.force !== undefined ? parseFloat(req.options.force) : 1,
					radius = req.options.radius !== undefined ? parseFloat(req.options.radius) : 100
				res.log('Exploding from center (force='+force+', radius='+radius+')');
				bubble.averageFuck(force, radius);
			});
		})
			.addDescription('Explode the bubble from the center of its mass')
			.addOption('force', 'f', 'Amount of force exerted')
			.addOption('radius', 'r', 'Size of the blast radius');
	};
});
define('portfolio-manager/module',[
	'./main',
	'./commands/view',
	'./commands/bubble'
], function (
	$portfolio,
	viewModule,
	bubbleModule

) {
	var SEP = '\t';
	return function(app) {

		app.portfolio = new $portfolio.PortfolioManager();
		app.output.async('PRELOAD\tportfolio items', function(res, rej) {
			return app.portfolio.load().then(function() {
				app.output.log();
				app.output.log('All done, loaded '+app.portfolio.list().length+' portfolio items.');
				res(true);
			}).catch(function(err) {
				app.output.log();
				app.output.log('Could not load portfolio items:');
				app.output.error(new Error(err.message));
				res(true);
			});
		});

		viewModule.call(this, app);
		bubbleModule.call(this, app);
	};
});
define('controllers/webcam',[], function() {

	function Webcam() {
		var element = document.createElement('video');
		element.setAttribute('autoplay', true);
		element.classList.add('webcam');
		this.element = element;
		this.stream = null;
	}

	Webcam.prototype.start = function(cb) {
		if(this.isActive())
			throw new Error('Already started');

		var video = this.element,
			self = this;

		navigator.getUserMedia = navigator.getUserMedia
			|| navigator.webkitGetUserMedia
			|| navigator.mozGetUserMedia
			|| navigator.msGetUserMedia
			|| navigator.oGetUserMedia;

		if (!navigator.getUserMedia)
			throw new Error('No user media');

		navigator.getUserMedia({video: true}, function (stream) {
			video.src = window.URL.createObjectURL(stream);
			self.stream = stream;
			if(cb)
				cb(null, this);
		}.bind(this), function (error) {
			console.log(error);
			if(cb)
				cb(new Error('Webcam access denied' + (error ? ': '+ (error.message || error.name) : '')));
		});
	};

	Webcam.prototype.stop = function() {
		if(!this.isActive())
			throw new Error('Already stopped');

		this.stream.stop();

		this.stream = null;
	};

	Webcam.prototype.isActive = function() {
		return !!this.stream;
	};

	return function(app) {
		var webcam = new Webcam();


		var webcamCommand = app.command.addCommand('webcam')
			.addDescription('Fux around with the webcam'),
			webcamWindow;

		webcamCommand.addCommand('on', function(req, res) {
			res.async('Accessing webcam', function(resolve, rej) {
				webcam.start(function(err, stream) {
					if(err) {
						res.error(err);
					} else {
						webcamWindow = app.window.openNewWindow('Webcam', webcam.element);
					}

					resolve(true);
				});
			});
		}).addDescription('Engage webcam');

		webcamCommand.addCommand('off', function(req, res) {
			webcam.stop();
			webcamWindow.destroy();
		}).addDescription('Disengage webcam');
	};

});
define('controllers/who',[
	'window-manager'
], function ($window) {
	var SEP = '\t';

	var profileBorn = new Date('July 10, 1988 8:00:00 GMT'),
		profileInformation = {
		name: 'Wybe Minnebo',
		gender: 'Male',
		born: profileBorn.toDateString() + ' ' + profileBorn.toTimeString(),
		nationality: 'NL (the Netherlands)'
	};

	return function(app) {
		app.command.addCommand('who', function(req, res) {

			res.log('Requesting WHOIS information on: Wybe Minnebo');
			res.log(SEP + 'Encrypting something very difficult');
			res.log(SEP + 'Request ID is NS@-0XEE-RWJ-B' + Math.floor(100000 + 899999 * Math.random()));
			res.async('Sattelite response decrypted.', function(resolve, reject) {
				setTimeout(function() {
					res.log();
					Object.keys(profileInformation).forEach(function(key) {
						res.keyValue(key, profileInformation[key]);
					});

					if(req.options.flat)
						return resolve(true);


					res.log();
					res.log('Opening WHOIS window...');
					require(['text!controllers/who.md'], function(wtfMd) {
						var window = new $window.MarkdownWindow('WHOIS', '0x.ee ~ wybe minnebo', wtfMd),
							image = new Image();
						image.src = 'images/mugshot.jpg';

						try {
							req.app.window.openNewWindow(window);
							window.documentElement.insertBefore(image, window.documentElement.firstChild);
							image.classList.add('pull-left');
						} catch (e) {
							res.error(e);
						}

						resolve(true);
					});

				}, 250 + 250 * Math.random())
			});

		})
			.addDescription('Find WHOIS info on the guy behind 0x.ee')
			.addOption('flat', 'f', 'Do not open profile in a window');
	};



});
define('controllers/pages',[], function () {
	return function (app) {


		// app.command.addCommand('info', function(req, res) {
		// 	res.log([
		// 		'ABOUT 0x.ee',
		// 		'-----------',
		// 		'',
		// 		'Works of code, illustration, CGI, video etc. displayed on this site are (c) wybe minnebo unless otherwise specified.',
		// 		'',
		// 		'0x.ee codebase 3rd party Bower dependencies',
		// 		'\tgyro.js',
		// 		'\tjquery',
		// 		'\tmarkdown',
		// 		'\tminimist (ported from npm)',
		// 		'\trequirejs',
		// 		'\trequirejs-text',
		// 		'',
		// 		'I tip my hat to the opensource community.',
		// 	])
		// })
		// 	.addDescription('Tells you what\'s what');

	};
});
define('controllers/motd',[], function () {
	return function(app) {

		app.command.addCommand('motd', function (req, res) {
//			res.log([
//				'         _______                                           _____                    _____          ',
//				'        /::\\    \\                ______                   /\\    \\                  /\\    \\         ',
//				'       /::::\\    \\              |::|   |                 /::\\    \\                /::\\    \\        ',
//				'      /::::::\\    \\             |::|   |                /::::\\    \\              /::::\\    \\       ',
//				'     /::::::::\\    \\            |::|   |               /::::::\\    \\            /::::::\\    \\      ',
//				'    /:::/~~\\:::\\    \\           |::|   |              /:::/\\:::\\    \\          /:::/\\:::\\    \\     ',
//				'   /:::/    \\:::\\    \\          |::|   |             /:::/__\\:::\\    \\        /:::/__\\:::\\    \\    ',
//				'  /:::/    / \\:::\\    \\         |::|   |            /::::\\   \\:::\\    \\      /::::\\   \\:::\\    \\   ',
//				' /:::/____/   \\:::\\____\\        |::|   |           /::::::\\   \\:::\\    \\    /::::::\\   \\:::\\    \\  ',
//				'|:::|    |     |:::|    | ______|::|___|___ ____  /:::/\\:::\\   \\:::\\    \\  /:::/\\:::\\   \\:::\\    \\ ',
//				'|:::|____|     |:::|    ||:::::::::::::::::|    |/:::/__\\:::\\   \\:::\\____\\/:::/__\\:::\\   \\:::\\____\\',
//				' \\:::\\    \\   /:::/    / |:::::::::::::::::|____|\\:::\\   \\:::\\   \\::/    /\\:::\\   \\:::\\   \\::/    /',
//				'  \\:::\\    \\ /:::/    /   ~~~~~~|::|~~~|~~~       \\:::\\   \\:::\\   \\/____/  \\:::\\   \\:::\\   \\/____/ ',
//				'   \\:::\\    /:::/    /          |::|   |           \\:::\\   \\:::\\    \\       \\:::\\   \\:::\\    \\     ',
//				'    \\:::\\__/:::/    /           |::|   |            \\:::\\   \\:::\\____\\       \\:::\\   \\:::\\____\\    ',
//				'     \\::::::::/    /            |::|   |             \\:::\\   \\::/    /        \\:::\\   \\::/    /    ',
//				'      \\::::::/    /             |::|   |              \\:::\\   \\/____/          \\:::\\   \\/____/     ',
//				'       \\::::/    /              |::|   |               \\:::\\    \\               \\:::\\    \\         ',
//				'        \\::/____/               |::|   |                \\:::\\____\\               \\:::\\____\\        ',
//				'         ~~                     |::|___|                 \\::/    /                \\::/    /        ',
//				'                                 ~~                       \\/____/                  \\/____/         '
//			])

			res.log([
				'----------------------------------------------------------',
				'      _          _      _              _            _',
				'    / /\\       /_/\\    /\\ \\           /\\ \\         /\\ \\',
				'   / /  \\      \\ \\ \\   \\ \\_\\         /  \\ \\       /  \\ \\',
				'  / / /\\ \\      \\ \\ \\__/ / /        / /\\ \\ \\     / /\\ \\ \\',
				' / / /\\ \\ \\      \\ \\__ \\/_/        / / /\\ \\_\\   / / /\\ \\_\\',
				'/_/ /  \\ \\ \\      \\/_/\\__/\\       / /_/_ \\/_/  / /_/_ \\/_/',
				'\\ \\ \\   \\ \\ \\      _/\\/__\\ \\     / /____/\\    / /____/\\',
				' \\ \\ \\   \\ \\ \\    / _/_/\\ \\ \\   / /\\____\\/   / /\\____\\/',
				'  \\ \\ \\___\\ \\ \\  / / /   \\ \\ \\ / / /______  / / /______',
				'   \\ \\/____\\ \\ \\/ / /    /_/ // / /_______\\/ / /_______\\',
				'    \\_________\\/\\/_/     \\_\\/ \\/__________/\\/__________/',
				'----------------------------------------------------------',
				'Welcome to 0x.ee v 3.0-rc1, it has regenerative javascript and extra-futuristic flavour. Though the command line interface doesn\'t feel as HTML5 as it actually is, CLI is the most powerful way of communicating with a \'puter.',
				'',
				'Here\'s some commands to get you started. You can also click on \'em:',
				'',
				'*  *  *  *',
				'',
				'YOU HAVE REACHED THE PORTFOLIO SITE OF WYBE MINNEBO',
				'interaction designer, javascript developer and what have you',
				'',
				'Click or type any of the following to begin:',
				'&#62;  <a command="help">help</a>  &#60;\tList all available commands, and helps you with them',
				'&#62;  <a command="view">view</a>  &#60;\tMy portfolio stuff! That\'s what the site is for, of course'

			]);
		})
			.addDescription('Runs at boot-time');

	};

});
require([
	'base64',
	'core',

	'sensor-manager/module',
	'portfolio-manager/module',

	'controllers/webcam',
	'controllers/who',
	'controllers/pages',
	'controllers/motd'

], function (
	base64,
	core,

	sensorModule,
	portfolioModule,

	webcamModule,
	whoModule,
	pagesModule,
	motdModule

	) {
	function Application(element) {
		core.Application.call(this, element);

		this.command.addDescription([
			'Welcome to 0x.ee... This site (or rather, application), works through written commands. For your viewing pleasure, any highlighted text is clickable as a shortcut to typing something.',
			'',
			'Click the "?" for more detailed information about a specific command.'
		]);


		var fakeLoadInfo = {
			time: window.performance.timing.domContentLoadedEventEnd - window.performance.timing.navigationStart,
			timestamp: new Date().getTime(),
			modules: [
				'sattelite firmware',
				'conferencing link',
				'telegraphy module',
				'TWS optical enchancer',
				'climate control',
				'burst creativity generator'
			],
			satLinkProtocol: '0x.ee://',
			satLinkConnected: false,
			satLinkStrategy: 'optimistic'
		};

		this.output.debug('Loaded 0x.ee system 3...', fakeLoadInfo);
		this.output.log([
			' ___ __ __   _____ _____    _____   ___   ___     _____ _____ ___   ',
			'|   |  |  | |   __|   __|  |  |  | |_  | |   |___| __  |     |_  |  ',
			'| | |-   -|_|   __|   __|  |  |  |_|_  |_| | |___|    -|   --|_| |_ ',
			'|___|__|__|_|_____|_____|   \\___/|_|___|_|___|   |__|__|_____|_____|'
		]);

		var ieVersion = detectIE();
		if(ieVersion) {
			this.output.error('Warning: You\'re using Internet Explorer '+ieVersion+'; some UI functionality may be broken. Recommended browsers are Chromium, Google Chrome or Mozilla Firefox, which are also all free.');
		}
		this.output.onceQueueFlushed(function() {
			var hashbang = (window.location.hash || '').trim();

			if(hashbang && hashbang.substr(0,3) === '#!/') {
				if(hashbang.substr(3,1) === '~')
					this.input.submit(base64.decode(hashbang.substr(4)));
				else
					this.input.submit(hashbang.substr(3));
			} else {
				this.input.submit('motd');
			}

		}.bind(this));

		[
			sensorModule,
			portfolioModule,

			webcamModule,
			whoModule,
			pagesModule,
			motdModule
		].forEach(function(module) {
			module(this);
		}.bind(this));

	}

	Application.prototype = Object.create(core.Application.prototype);
	Application.prototype.constructor = Application;

	var app = new Application();


	// http://stackoverflow.com/questions/19999388/jquery-check-if-user-is-using-ie
	function detectIE() {
		var ua = window.navigator.userAgent;
		var msie = ua.indexOf('MSIE ');
		var trident = ua.indexOf('Trident/');

		if (msie > 0) {
			// IE 10 or older => return version number
			return parseInt(ua.substring(msie + 5, ua.indexOf('.', msie)), 10);
		}

		if (trident > 0) {
			// IE 11 (or newer) => return version number
			var rv = ua.indexOf('rv:');
			return parseInt(ua.substring(rv + 3, ua.indexOf('.', rv)), 10);
		}

		// other browser
		return false;
	}

	window.app = app;


	//app.portfolio.list()[5].create({ app: app });
});
define("app", function(){});
}());